(ns compiler.core
  (:refer-clojure :exclude [compile])
  (:gen-class)
  (:use [clojure.java.io])
  (:require [compiler.io :as io]
            [compiler.parser :as parser]
            [clojure.set :as set]
            [flatland.ordered.map :as ordered-map]
            [fast-zip.core :as zip]
            [clojure.walk :as walk]
            [clojure.stacktrace :as stacktrace]
            [clojure.pprint :as pprint]
            [clj-jgit.util :as jgit-util]
            [clj-jgit.porcelain :as jgit]
            [clojure.tools.cli :refer [parse-opts]]
            [watchtower.core :as watcher])
  (:use [compiler [template :only [render-template]]]
        [clojure.java.shell]
        [clojure.tools [logging :only [warn info]]]))

(System/setProperty "org.slf4j.simpleLogger.showLogName" "false")
(System/setProperty "org.slf4j.simpleLogger.showDateTime" "true")
(System/setProperty "org.slf4j.simpleLogger.dateTimeFormat" "HH:mm:ss")
(System/setProperty "org.slf4j.simpleLogger.showThreadName" "false")

(defn append-to! [r ks v]
  (let [cv (reduce (fn[h v] (v h)) @r ks)]
    (swap! r assoc-in ks (conj cv v))
    ""))
(defn read-clojure-file [f]
  (let [ns (gensym)
        ns-str (str ns)]
    (create-ns ns)
    (binding [*ns* (the-ns ns)]
      (refer 'clojure.core)
      (-> (read-string (str \( (io/read-file f) \)))
          (parser/transform
           symbol?
           #(if (= (namespace %) ns-str)
              (-> % name symbol)
              %))
          ;;replace clojure.core/fn with fn
          ;;replace clojure.core/while with while
          (parser/transform
           (fn [x]
             (and (parser/form? 'quote x)
                  (or (= 'clojure.core/fn    (second x))
                      (= 'clojure.core/defn  (second x))
                      (= 'clojure.core/while (second x)))))
           (fn [[_ s]] `'~(-> s name symbol)))))))
(defn expand-reader-macros [form]
  (-> form
      (parser/transform
       (parser/form? 'clojure.core/deref)
       (fn [f] (cons 'deref (rest f))))
      (parser/transform
       map?
       (fn [x]
         (->> (seq x)
              (reduce
               (fn[h [k v]]
                 (conj h k v)) [])
              (seq)
              (cons 'fir-new-map))))))
(defn macro-normalize [f]
  (parser/transform f
                    (parser/form? 'let)
                    (fn [[_ bindings & body]]
                      `(~'let* ~(apply list bindings) ~@body))))
(defn expand-macros-single [form]
  (let [core-macros (->> (read-clojure-file "ferret/core.clj")
                         (filter (parser/form? 'defmacro)))
        core-macro-symbols (into #{} (map second core-macros))
        form-macros (->> (filter (parser/form? 'defmacro) form)
                         (filter (fn [[_ name]]
                                   (not (core-macro-symbols name)))))
        form-macro-symbols (map second form-macros)
        form (parser/drop form (parser/form? 'defmacro))
        temp-ns (gensym)
        macro-symbols (concat core-macro-symbols form-macro-symbols)]

    (create-ns temp-ns)
    (binding [*ns* (the-ns temp-ns)]
      (refer 'clojure.core :exclude (concat macro-symbols ['fn 'def]))
      (use '[compiler.io :only [exit-failure]])
      (use '[compiler.core :only [symbol-conversion]])
      (use '[compiler.parser :only [new-fir-fn]])

      (doseq [m (concat core-macros form-macros)]
        (eval m)))

    (let [form (-> form
                   (macro-normalize)
                   (expand-reader-macros)
                   (parser/transform
                    (fn [f]
                      (some true? (map #(parser/form? % f) macro-symbols)))
                    (fn [f]
                      (binding [*ns* (the-ns temp-ns)]
                        (-> (walk/macroexpand-all f)
                            ;;strip ns from symbols
                            (parser/transform symbol? #(-> % name symbol)))))))]
      (remove-ns temp-ns)
      form)))

(defn expand-macros-aux [form]
  (loop [f form]
    (let [expanded (expand-macros-single f)]
      (if (= f expanded)
        expanded
        (recur expanded)))))

(def expand-macros (memoize expand-macros-aux))
(defn shake-concat
  ([header form]
   (let [shakeable? (fn [f]
                      (or (parser/form? 'defn f)
                          (parser/form? 'defnative f)))
         header-symbols (->> (parser/peek header seq?)
                             (parser/symbol-set))
         header-fns (->> (parser/peek header shakeable?)
                         (map #(vector (second %) %))
                         (into {}))
         header-non-shakeable (parser/drop header shakeable?)
         form-expanded (expand-macros (concat header-non-shakeable form))
         fns (atom #{})
         _ (shake-concat form-expanded header-fns fns header-non-shakeable)
         header-shaked (parser/drop header (fn [f]
                                             (and (shakeable? f)
                                                  (not (@fns (second f))))))]
     (concat header-shaked form)))
  ([form built-in fns non-shakeable]
   (parser/transform form symbol?
                     #(do
                        (if-let [f (built-in %)]
                          (when (not (@fns %))
                            (swap! fns conj %)
                            (shake-concat (expand-macros (concat non-shakeable f))
                                          built-in fns non-shakeable))) %))))
(defn escape-fn-calls [form]
  (let [arity (parser/peek
               form
               (fn [f]
                 (and (parser/form? 'fir-defn-heap f)
                      (-> (parser/peek f (parser/form? 'fir-defn-arity))
                          (empty?)
                          (not )))))
        arity (reduce
               (fn [h [_ name _ _ [_ dispatch [_ default]] :as form]]
                 (let [jmp (if default
                             {:default default}
                             {})
                       jmp (reduce (fn[h [arity [_ call]]]
                                     (assoc h arity call))
                                   jmp dispatch)]
                   (assoc h name jmp)))
               {} arity)
        arity-renames (reduce (fn [h [name jmps]]
                                (reduce
                                 (fn [h jump]
                                   (assoc h jump (gensym (str name "__"))))
                                 h (vals jmps)))
                              {} arity)]
    (-> form
        ;; resolve arity calls
        (parser/transform
         (parser/form? 'fir-defn-arity)
         (fn [f]
           (parser/transform f
                             (parser/form? 'fir-fn-heap)
                             (fn [[_ & f]]
                               `(~'fir-fn-stack ~@f)))))
        (parser/transform
         (fn [f]
           (and (seq? f)
                (parser/form? 'fir-fn-heap (first f))
                (arity (-> f first second))))
         (fn [f]
           (let [[[_ fn] & args] f
                 dispatch ((arity fn) (count args))
                 default  ((arity fn) :default)]
             (cond dispatch `((~'fir-fn-heap ~dispatch) ~@args)
                   default  `((~'fir-fn-heap ~default)  ~@args)
                   :default f))))
        (parser/transform
         (fn [f]
           (and (symbol? f)
                (arity-renames f)))
         (fn [f]
           (arity-renames f)))
        ;; resolve fn calls
        (parser/transform
         (fn [f]
           (and (seq? f)
                (parser/form? 'fir-fn-heap (first f))))
         (fn [f]
           (let [[[_ & fn] & args] f]
             `((~'fir-fn-stack ~@fn) ~@args)))))))
(defn escape-fn-inheritance [form]
  (let [heap-fns (->> (parser/peek form (parser/form? 'fir-fn-heap))
                      (map second)
                      (into #{}))
        stack-fns (->> (parser/peek form (parser/form? 'fir-fn-stack))
                       (map second)
                       (into #{}))
        escapeable-fns (set/difference stack-fns heap-fns)]
    (parser/transform form
                      (fn [f]
                        (and (seq? f)
                             (= (first f) 'fir-defn-heap)
                             (escapeable-fns (second f))))
                      (fn [[_ & f]]
                        `(~'fir-defn-stack ~@f)))))
(defn import-modules-select-require [form]
  (let [norm-require (fn [f]
                       (if (symbol? f)
                         [f :as f]
                         f))]
    (->> (parser/peek form (parser/form? 'require))
         (reduce (fn[h v]
                   (if (= 2 (count v))
                     ;; require single module
                     (conj h (norm-require (->> v last last)))
                     ;; require multiple modules
                     (concat h (map #(norm-require (last %)) (rest v))))) [])
         (map (fn [[mod _ as]] [mod as]))
         (reduce (fn[h [mod as]]
                   (if (h mod)
                     (assoc h mod (conj (h mod) as))
                     (assoc h mod [as]))) {}))))
(defn import-modules-load-modules [package-list options]
  (->> package-list
       (reduce (fn[h [m aliases]]
                 (let [file-name      (str (.replace (str m) "." "/") ".clj")
                       mod            (-> (if (clojure.java.io/resource file-name)
                                            file-name
                                            (str (:path options) file-name))
                                          (read-clojure-file)
                                          (parser/drop (parser/form? 'configure-runtime!))
                                          (parser/drop (parser/form? 'configure-ferret!)))
                       macro-symbols  (->> (parser/peek mod (parser/form? 'defmacro))
                                           (map second)
                                           (into #{}))
                       def-symbols    (->> (parser/peek (expand-macros mod) (parser/form? 'def))
                                           (map second)
                                           (into #{}))
                       replace?       (set/union macro-symbols def-symbols)
                       mod            (parser/transform
                                       mod
                                       #(and (symbol? %)
                                             (replace? %))
                                       #(parser/new-symbol m "_" %))]
                   (reduce (fn [h v] (conj h v)) h mod)))
               [])
       lazy-seq))
(defn import-modules-convert-alias-to-module [package-list form]
  (let [alias-to-mod (reduce (fn[h [mod aliases]]
                               (reduce (fn[h v] (assoc h v mod)) h aliases))
                             {} package-list)]
    (parser/transform form symbol?
                      (fn [f]
                        (if-let [[_ alias fn] (re-find #"(.*?)/(.*)" (str f))]
                          (if-let [mod-sym (alias-to-mod (symbol alias))]
                            (parser/new-symbol mod-sym "_" fn)
                            f)
                          f)))))
(defn import-modules [form options]
  (let [package-list (import-modules-select-require form)
        form         (parser/drop form (parser/form? 'require))
        modules      (import-modules-load-modules package-list options)
        non-public?  (->> modules
                          (reduce (fn[private-symbols mod]
                                    (-> mod
                                        (parser/peek #(and (symbol? %)
                                                           (-> % meta :private)))
                                        (concat private-symbols))) [])
                          (into #{}))
        form         (import-modules-convert-alias-to-module package-list form)
        violations   (parser/peek form #(non-public? %) #(zip/node (zip/up %)))]
    (when (not (empty? violations))
      (doseq [v violations]
        (warn "non-public-access =>" v))
      (io/exit-failure))
    (shake-concat modules form)))

(defn import-modules-all [form options]
  (loop [f form]
    (let [expanded (import-modules f options)]
      (if (= f expanded)
        expanded
        (recur expanded)))))
(defn ferret-runtime [options form]
  (->> (-> form
           (import-modules-all options)
           (expand-reader-macros))
       (shake-concat (read-clojure-file "ferret/core.clj"))
       ;; tag form with the build info
       (cons `(~'native-define ~(try
                                  (let [version (io/read-file-from-url "build.info")]
                                    (str "// ferret-lisp " version))
                                  (catch Exception e
                                    (str "// ferret-lisp")))))))
(defn let-closure [bindings body]
  (if (empty? bindings)
    `((~'fir-let-fn () ~@body))
    (apply
     (fn close [[arg val] & more]
       (if (empty? more)
         `((~'fir-let-fn [~arg] ~@body) ~val)
         `((~'fir-let-fn [~arg] ~(apply close more)) ~val)))
     (partition 2 bindings))))

(defn let-assert [bindings body]
  (when (odd? (count bindings))
    (warn
     (str "let requires an even number of forms in binding vector => " bindings))
    (io/exit-failure)))

(defn let->fn [form]
  (-> form

      (parser/transform (parser/form? 'let*)
                        (fn [[_ bindings & body]]
                          (let-assert bindings body)
                          (let-closure bindings body)))

      (parser/transform (parser/form? 'fir-let-fn)
                        (fn [[_ args & body]]
                          (parser/new-fir-fn :args args :body body)))))
(defn do->fn [form]
  (parser/transform form
                    (parser/form? 'do)
                    (fn [f] `(~(parser/new-fir-fn :body (rest f))))))
(defn fn-defined? [fns env args body]
  (if-let [fn-name (@fns (concat [env args] body))]
    (apply list 'fir-fn-heap fn-name env)))

(defn define-fn [fns env name args body]
  (let [n (if name
            name
            (gensym "FN__"))]
    (swap! fns assoc (concat [env args] body) n)
    (apply list 'fir-fn-heap n env)))

(defn fn->lift
  ([form]
   (let [fns  (atom (ordered-map/ordered-map))
         form (fn->lift form fns)
         fns  (map (fn [[body name]] (concat ['fir-defn-heap name] body)) @fns)]
     (concat fns form)))
  ([form fns & [env]]
   (parser/transform
    form
    (parser/form? 'fn*)
    (fn [sig]
      (let [[name args body] (parser/split-fn sig)
            ;; transform named recursion in body
            body (if name
                   (parser/transform
                    body
                    (parser/form? name)
                    (fn [[_ & args]]
                      (cons
                       (apply list 'fir-fn-heap name env)
                       args)))
                   body)
            body (fn->lift body fns (concat args env))
            symbols (parser/symbol-set body)
            env  (->> (set/intersection
                       symbols
                       (into #{} (flatten env)))
                      (into ()))

            args (if (parser/ffi-fn?
                      (filter #(not (parser/form? 'native-declare %)) body))
                   args
                   (parser/transform args
                                     symbol?
                                     (fn [v]
                                       (if (or (not (parser/fn-arg-symbol? v))
                                               (symbols v))
                                         v '_))))]
        (if-let [n (fn-defined? fns env args body)]
          n
          (define-fn fns env name args body)))))))
(defn escape-cpp-symbol [s]
  (clojure.string/escape
   (str s)
   {\- \_ \* "_star_" \+ "_plus_" \/ "_slash_"
    \< "_lt_" \> "_gt_" \= "_eq_" \? "_QMARK_"
    \! "_BANG_" \# "_"}))

(defn symbol-conversion [form]
  (let [c (comp #(symbol (escape-cpp-symbol %))
                #(cond (= 'not %) '_not_
                       :default %))]
    (parser/transform form symbol? c)))
(defn remove-assertions [options form]
  (if (:release options)
    (do (info "option => release mode")
        (parser/drop form (parser/form? 'assert)))
    form))
(defn inline-defn? [f]
  (and (parser/form? 'def f)
       (-> f second meta :tag (not= 'volatile))
       (parser/form? 'fir-fn-heap
                     (->> f (drop 2) first))))

(defn fn->inline [options form]
  (if (:global-functions options)
    form
    (let [defns      (->> (parser/peek form inline-defn?)
                          (filter #(= 2 (-> % last count))))
          fn-table   (map (fn [[_ name [_ gensym]]] [name gensym]) defns)
          impl-table (apply hash-map (flatten fn-table))
          defn?      (fn [f]
                       (and (inline-defn? f)
                            (impl-table (second f))))
          invoke     #(if-let [imp (impl-table %)]
                        (list 'fir-fn-heap imp)
                        %)
          no-defn    (reduce (fn[h v] (parser/drop h defn?)) form defns)
          inlined    (reduce (fn[h [name gensym]]
                               (parser/transform h
                                                 #(or (parser/form? name %)
                                                      (parser/form? 'def %))
                                                 (fn [f] (map invoke f))))
                             no-defn fn-table)]
      (reduce (fn[h [name gensym]]
                (parser/transform h #(and (symbol? %)
                                          (= % gensym))
                                  (fn [_] (identity name))))
              inlined fn-table))))
(defn escape-analysis [form]
  (->> form
       (escape-fn-calls)
       (escape-fn-inheritance)))
(defn compile [form options]
  (->> (ferret-runtime options form)
       (remove-assertions options)
       (expand-macros)
       (let->fn)
       (do->fn)
       (fn->lift)
       (fn->inline options)
       (escape-analysis)
       (symbol-conversion)))
(defmulti emit (fn [_ f _]
                 (cond (parser/form? '(fir_fn_stack list) f)   'fir_inline_list
                       (parser/form? '(fir_fn_stack first) f)  'fir_inline_first
                       (parser/form? '(fir_fn_stack rest) f)   'fir_inline_rest
                       (parser/form? 'fir_defn_heap f)   'fir_defn_heap
                       (parser/form? 'fir_defn_stack f)  'fir_defn_stack
                       (parser/form? 'fir_defn_arity f)  'fir_defn_arity
                       (parser/form? 'fir_fn_heap f)     'fir_fn_heap
                       (parser/form? 'fir_fn_stack f)    'fir_fn_stack
                       (parser/form? 'list f)            'list
                       (parser/form? 'defobject f)       'defobject
                       (parser/form? 'matrix f)          'matrix
                       (parser/form? 'native_header f)   'native_header
                       (parser/form? 'native_declare f)  'native_declare
                       (parser/form? 'native_define f)   'native_define
                       (parser/form? 'if f)              'if
                       (parser/form? 'def f)             'def
                       (parser/form? 'fir_new_map f)     'fir_new_map
                       (symbol? f)                 :symbol
                       (keyword? f)                :keyword
                       (number? f)                 :number
                       (nil? f)                    :nil
                       (char? f)                   :char
                       (string? f)                 :string
                       (instance?
                        java.util.regex.Pattern f) :regex-pattern
                       (or (true? f) (false? f))   :boolean
                       (seq? f)                    :invoke-fn
                       :default                    :unsupported-form)))

(defmethod emit :unsupported-form [_ form _]
  (warn "unsupported form =>" form)
  (io/exit-failure))

(defn emit-ast [options ast state]
  (reduce (fn[h v] (conj h (emit options v state))) [] ast))
(defn emit-source [form options]
  (let [state (atom {:native-headers []
                     :native-declarations []
                     :objects []
                     :symbol-table #{}
                     :lambdas []
                     :native-defines []})
        ast (compile form options)
        body (emit-ast options ast state)]
    (when (:ast options)
      (pprint/pprint ast))
    (assoc @state :body body)))
(defmethod emit :symbol [_ form state] (str form))

(defmethod emit :string [_ form state]
  (str "obj<string>(\"" (io/escape-string form) "\"," (count form) ")"))

(defmethod emit :boolean [_ form state]
  (if (true? form)
    (str "cached::true_o")
    (str "cached::false_o")))

(defmethod emit :nil [_ form state] "nil()")

(defmethod emit :keyword [_ form _]
  (str "obj<keyword>(" (reduce (fn[h v] (+ h (int v))) 0 (str form)) ")"))

(defmethod emit :char [_ form state] (str "obj<number>(" (int form) ")"))

(defmethod emit :number [_ form state] (str "obj<number>(" (double form) ")"))

(defmethod emit 'fir_new_map [options [_ & kvs] state]
  (let [kvs (partition 2 kvs)
        keys (->> (map first kvs)
                  (map #(emit options % state))
                  (interpose \,))
        vals (->> (map second kvs)
                  (map #(emit options % state))
                  (interpose \,))]
    (str "obj<map_t>("
         "rt::list(" (apply str keys) "),"
         "rt::list(" (apply str vals) "))")))

(defmethod emit :regex-pattern [options regex state]
  (emit options
        (org.apache.commons.lang.StringEscapeUtils/unescapeJava
         (str regex))
        state))
(defmethod emit 'def [options [_ name & form] state]
  (append-to! state [:symbol-table] name)
  (str "(" name " = " (apply str (emit-ast options form state)) ")"))

(defmethod emit 'if [options [_ cond t f] state]
  (let [cond (emit options cond state)
        t (emit options t state)
        f (if (nil? f) "nil()" (emit options f state))]
    (apply str "(" cond " ? " t " : " f ")")))

(defn defobject [name f options]
  (let [def (io/read-file (first f) options)]
    (render-template
     "#ifndef FERRET_OBJECT_$guard$
      #define FERRET_OBJECT_$guard$
       $body$
      #endif"
     :guard       (.toUpperCase (str name))
     :body        def)))

(defmethod emit 'list [options [fn & args] state]
  (let [elements  (->> (emit-ast options args state)
                       (interpose \,)
                       (apply str))]
    (str "rt::list(" elements ")")))

(defmethod emit 'defobject [options [_ name & spec] state]
  (append-to! state [:objects] (defobject name spec options)))

(defmethod emit 'matrix [options [_ elements] state]
  (let [rows (count elements)
        cols (-> elements first count)
        elements (apply concat elements)
        elements (map #(if (number? %)
                         (str "real_t(" % ")")
                         (str
                          "number::to<real_t>"
                          "(" (emit options % state) ")"))
                      elements)
        elements (apply str (interpose \, elements))
        matrix-t (str "size_t(" rows "), size_t(" cols ")," elements)
        matrix-decl (str "obj<matrix_t>(" matrix-t ")")]
    matrix-decl))

(defmethod emit 'native_header [_ [_ & declarations] state]
  (append-to! state [:native-headers] declarations))

(defmethod emit 'native_declare [_ [_ declaration] state]
  (append-to! state [:native-declarations] declaration))

(defmethod emit 'native_define [_ [_ define] state]
  (append-to! state [:native-defines] define))
(defmethod emit 'fir_inline_list [options [_ & args] state]
  (str "rt::list(" (apply str (interpose \, (emit-ast options args state))) ")"))

(defmethod emit 'fir_inline_first [options [_ & seq] state]
  (str "rt::first(" (apply str (emit-ast options seq state)) ")"))

(defmethod emit 'fir_inline_rest [options [_ & seq] state]
  (str "rt::rest(" (apply str (emit-ast options seq state)) ")"))
(defn norm-fn-env [env]
  (->> env
       (flatten)
       (filter #(and (not (= '& %))
                     (not (= '_ %))
                     (not (= :as %))))))

(defn new-fn-heap [l]
  (let [n (second l)
        e (norm-fn-env (drop 2 l))]
    (if (empty? e)
      (str "obj<" n ">()")
      (str "obj<" n ">(" (apply str (interpose \, e)) ")"))))

(defn new-fn-stack [l]
  (let [n (second l)
        e (norm-fn-env (drop 2 l))]
    (if (empty? e)
      (str n "()")
      (str n "(" (apply str (interpose \, e)) ")"))))

(defn invoke-fn [n args]
  (if (empty? args)
    (str "run(" n ")")
    (str "run(" n ","  (apply str (interpose \, args))")")))
(declare destructure-arguments)

(defn destructure-nth-rest [parent pos]
  (reduce (fn[h v] (str v "(" h ")")) parent (repeat pos "rt::rest")))

(defn destructure-nth [parent pos]
  (str "rt::first(" (destructure-nth-rest parent pos) ")"))

(defn destructure-get [name parent key]
  (str "ref " name " = "
       parent ".cast<map_t>()->val_at(rt::list(" (emit nil key nil) "));"))

(defn new-fn-arg [name parent pos]
  (let [value (destructure-nth parent pos)
        tag   (-> name meta :tag)]
    (condp = tag
      'bool_t     (str "bool " name " = " "bool(" value ")")
      'real_t     (str "real_t " name " = " "number::to<real_t>(" value ")")
      'number_t   (str "number_t " name " = " "number::to<number_t>(" value ")")
      'size_t     (str "size_t " name " = " "number::to<size_t>(" value ")")
      'byte       (str "byte " name " = " "number::to<byte>(" value ")")
      'c_str      (str "var " name "_packed = string::pack(" value ");\n"
                       "char* " name " = " "string::c_str(" name "_packed)")
      'matrix     (str "matrix &" name " = " "value<matrix>::to_reference(" value ")")
      (str "ref " name " = " value))))

(defn new-fn-var-arg [name parent pos]
  (str "ref " name " = " (destructure-nth-rest parent pos)))

(defn destructure-associative [name parent pos]
  (let [tmp-name (gensym)]
    [(new-fn-arg tmp-name parent pos)
     (map (fn [[s k]] (destructure-get s tmp-name k)) name)]))

(defn destructure-sequential [args parent]
  (reduce
   (fn [h [pos name]]
     (let [name (cond
                  (symbol? name)
                  (new-fn-arg name parent pos)

                  (parser/form? 'fir_destructure_associative name)
                  (let [[_ & args ] name
                        args (->> args
                                  (partition 2)
                                  (remove #(= (first %) '_))
                                  flatten
                                  (apply hash-map))]
                    (destructure-associative args parent pos))

                  (coll?   name)
                  (destructure-arguments name (destructure-nth parent pos)))]
       (conj h name))) [] args))

(defn destructure-var-args [name parent pos]
  (cond (nil?     name)  []
        (symbol?  name)  (new-fn-var-arg name parent pos)
        (coll?    name)  (let [tmp-name (gensym)]
                           [(new-fn-var-arg tmp-name parent pos)
                            (destructure-arguments name tmp-name)])))

(defn destructure-as-arg [name parent]
  (if (symbol?     name)
    (new-fn-var-arg name parent 0)
    []))

(defn destructure-arguments
  ([args]
   (->> (destructure-arguments args "_args_") flatten))
  ([args parent]
   (let [t-args         args
         args           (take-while #(and (not= % '&) (not= % :as)) t-args)
         var-args       (->> t-args (drop-while #(not= % '&)) second)
         as-arg         (->> t-args (drop-while #(not= % :as)) second)
         args-indexed   (->>  args
                              (map-indexed (fn [p v] [p v]))
                              (filter #(not= (second %) '_)))
         as-arg         (destructure-as-arg as-arg parent)
         var-args       (destructure-var-args var-args parent (count args))
         args           (destructure-sequential args-indexed parent)]
     [args var-args as-arg])))
(defmethod emit :invoke-fn [options [fn & args] state]
  (invoke-fn (emit options fn state) (emit-ast options args state)))

(defmethod emit 'fir_fn_heap [_ f state]
  (new-fn-heap f))

(defmethod emit 'fir_fn_stack [_ f state]
  (new-fn-stack f))

(defn emit-lambda [options name env args body state]
  (let [native-declarations (filter (parser/form? 'native_declare) body)
        return (fn [b] (conj (pop b) (str "return " (last b))))
        body (filter #(not (parser/form? 'native_declare %)) body)
        body (cond  (empty? body)
                    ["return nil()"]
                    ;; multi arity dispacth
                    (parser/form? 'fir_defn_arity (first body))
                    (return
                     (emit options (first body) state))
                    ;; ffi call
                    (parser/ffi-fn? body)
                    (let [buffer (StringBuilder.)]
                      (doseq [b body]
                        (.append buffer b))
                      (let [body (.toString buffer)]
                        (cond (.contains body "__result")
                              ["var __result" body "return __result"]
                              (.contains body "return")
                              [body]
                              :default [body "return nil()"])))
                    ;; s-expression
                    :default (return
                              (emit-ast options body state)))
        env  (norm-fn-env env)
        vars (destructure-arguments args)]
    (doseq [dec native-declarations] 
      (emit options dec state))
    {:name name :env env :args args :vars vars :body body}))

(defmethod emit 'fir_defn_heap [options [_ name env args & body] state]
  (append-to! state [:lambdas] (emit-lambda options name env args body state)))

(defmethod emit 'fir_defn_stack [options [_ name env args & body] state]
  (append-to! state [:lambdas] (-> (emit-lambda options name env args body state)
                                   (assoc :stack true))))
(defmethod emit 'fir_defn_arity [_ [_ switch default] state]
  (let [default (if default
                  (str (new-fn-stack default) ".invoke(_args_)")
                  "nil()")
        switch  (render-template
                 "switch(rt::count(_args_)) {
                  $fns: {fn|
                    case $fn.case$ :
                       return $fn.fn$.invoke(_args_); };separator=\"\n\"$
                  }"
                 :fns (map (fn [[s f]] {:fn (new-fn-stack f) :case s}) switch))]
    [switch default]))
(defn lambda-definitions [fns]
  (render-template
   "$fns: {fn|
      $if(!fn.stack)$
       class $fn.name$ final : public lambda_i{
      $else$
       class $fn.name$  \\{
      $endif$
        $fn.env:{const var $it$;} ;separator=\"\n\"$
      public:
        $if(fn.env)$
          explicit $fn.name$ ($fn.env:{ref $it$} ;separator=\",\"$) :
            $fn.env:{$it$($it$)} ;separator=\",\"$ { }
        $endif$

        var invoke (ref _args_) const $if(!fn.stack)$ final $endif$ ;
      };};separator=\"\n\n\"$"
   :fns fns))

(defn lambda-implementations [fns]
  (render-template
   "$fns: {fn|
      inline var $fn.name$::invoke (ref _args_) const {
        (void)(_args_);
        $fn.vars:{$it$;} ;separator=\"\n\"$

        $fn.body:{$it$;} ;separator=\"\n\"$
      }
     };separator=\"\n\n\"$"
   :fns fns))
(defn program-template [source options]
  (let [{:keys [body lambdas symbol-table native-headers objects
                native-declarations native-defines]} source
        native-headers (->> native-headers flatten (into #{}))
        file-ns        (-> options :base-name escape-cpp-symbol)
        main           (render-template
                        (io/read-file "main.cpp")
                        :file       file-ns)]
    (render-template
     "
        $native_defines:{$it$} ;separator=\"\n\"$
        $native_headers:{#include \"$it$\"} ;separator=\"\n\"$

        #ifndef FERRET_RUNTIME_H
        #define FERRET_RUNTIME_H
         $ferret_h$
        #endif

        // Objects
        namespace ferret{
         $objects:{$it$} ;separator=\"\n\"$
        }

        // Symbols
        namespace $file${
         using namespace ferret;

         #if defined(ARDUINO)
           typedef ferret::boolean boolean;
         #endif

         $symbols:{var $it$;} ;separator=\"\n\"$
        }

        $native_declarations:{$it$} ;separator=\"\n\"$

        // Runtime Implementations
        #ifndef FERRET_RUNTIME_CPP
        #define FERRET_RUNTIME_CPP
         $ferret_cpp$
        #endif

        // Lambda Prototypes
        namespace $file${
          $lambda_classes:{$it$} ;separator=\"\n\"$
        }

        // Command Line Arguments
        #if defined(FERRET_STD_LIB) &&               \\
            !defined(FERRET_DISABLE_CLI_ARGS) &&     \\
            !defined(FERRET_DISABLE_STD_MAIN)
          ferret::var _star_command_line_args_star_;
        #endif

        // Lambda Implementations
        namespace $file${
          $lambda_bodies:{$it$} ;separator=\"\n\"$
        }

        // Program Run
        namespace $file${
         void main(){
          $body:{$it$;} ;separator=\"\n\"$ 
         }
        }

        $ferret_main$"
     :file                 file-ns
     :native_defines       native-defines
     :ferret_h             (io/read-file "runtime.h")
     :native_headers       native-headers
     :objects              objects
     :symbols              symbol-table
     :native_declarations  native-declarations
     :ferret_cpp           (io/read-file "runtime.cpp")
     :lambda_classes       (lambda-definitions lambdas)
     :lambda_bodies        (lambda-implementations lambdas)
     :body                 (filter #(not (empty? %)) body)
     :ferret_main          main)))
(defn checkout-deps [path]
  (when (io/file-exists (str path "/deps.clj"))
    (let [deps (-> (read-clojure-file "deps.clj")
                   (parser/peek (parser/form? 'git)))
          deps (map (fn [[_ & kvs]] (apply hash-map kvs)) deps)]
      (doseq [{url :url commit :commit} deps]
        (let [folder (str path (jgit-util/name-from-uri url))]
          (info "dep =>" url)
          (when (io/file-exists folder)
            (org.apache.commons.io.FileUtils/deleteDirectory
             (java.io.File. folder)))
          (let [repo (jgit/git-clone-full
                      url (org.apache.commons.io.FilenameUtils/normalize folder))]
            (jgit/git-checkout (:repo repo)
                               (if commit
                                 commit
                                 "master"))))))))
(defn compile-options [& [options]]
  (merge {:compiler "g++"
          :compiler-options ["-std=c++11"]
          :source-extension io/extension-cpp
          :base-name "solution"
          :binary-file "solution"}
         options))

(defn file-name [options]
  (str (:base-name options) "." (:source-extension options)))

(defn cpp-file-name [options]
  (str (:output-path options) (file-name options)))
(defn compile-options-parse-source [file]
  (try
    (let [program (slurp file)
          options (->> program
                       (re-seq #"(?s)build-conf-begin.*?//(.*?)// build-conf-end")
                       (map second)
                       (map #(.replaceAll % "//" ""))
                       (map #(.replaceAll % "\n" " "))
                       (map read-string))
          keys (->> options
                    (map #(keys %))
                    flatten
                    (into #{})
                    (into []))
          combine (fn [key]
                    (->> options
                         (reduce (fn[h v]
                                   (if (nil? (key v))
                                     h
                                     (apply merge (flatten [h (key v)])))) #{})
                         (into [])))]
      (compile-options
       (reduce (fn[h v]
                 (assoc h v (combine v))) {} keys)))
    (catch Exception e
      (compile-options {}))))
(defn build-specs [input args]
  (fn []
    (let [args             (fn [k]
                             (->> args :options k))
          output           (if (args :output)
                             (args :output)
                             input)
          output-path      (io/file-path output)
          output-extension (if (args :output) 
                             (io/file-extension (args :output))
                             io/extension-cpp)
          base-name        (io/file-base-name output)
          input-path       (io/file-path input)
          output-file      (io/make-file output-path base-name output-extension)
          binary-file      (if (args :binary) 
                             (args :binary)
                             base-name)
          default-options  (compile-options-parse-source output-file)]
      (-> default-options
          (assoc :input-file         input)
          (assoc :base-name          base-name)
          (assoc :path               input-path)
          (assoc :output-path        output-path)
          (assoc :source-extension   output-extension)
          (assoc :binary-file        binary-file)
          (assoc :ast                (args :ast))
          (assoc :compile-program    (args :compile))
          (assoc :release            (args :release))
          (assoc :format-code        (not (args :disable-formatting)))
          (assoc :global-functions   (args :global-functions))
          (assoc :extra-source-files
                 (cond (not (empty? (:arguments args)))
                       (:arguments args)
                       (not (empty? (:extra-source-files default-options)))
                       (:extra-source-files default-options)
                       :default []))))))
(defn compile->cpp [form options]
  (let [file-name (cpp-file-name options)
        source    (emit-source form options)
        program   (program-template source options)]
    (io/write-to-file file-name program)
    (info "compiled" "=>" file-name)
    true))
(defn cxx-compiler [options]
  (let [compiler    (if (System/getenv "CXX")
                      (System/getenv "CXX")
                      (:compiler options))
        env-options (if (System/getenv "CXXFLAGS")
                      (seq (.split (System/getenv "CXXFLAGS") " ")))
        options     (->> (:compiler-options options) (map str))]
    [compiler (concat options env-options)]))
(defn cxx-command [options]
  (if (:command options)
    (flatten ["/usr/bin/env" "sh" "-c" (:command options)])
    (let [[cxx cxx-options] (cxx-compiler options)
          source-files  (map #(let [extension (io/file-extension %)]
                                [(cond (= extension "c") ["-x" "c"]
                                       (= extension "c++") ["-x" "c++"]
                                       :default "")
                                 %])
                             (:extra-source-files options))]
      (flatten [cxx cxx-options source-files
                ["-x" "c++"] (file-name options)
                ["-o" (:binary-file options)]]))))
(defn compile->binary [options]
  (let [command (cxx-command options)]
    (info "building" "=>" (apply str (interpose " " command)))
    (let [build-dir (:output-path options)
          ret (try
                (with-sh-dir build-dir
                  (apply sh command))
                (catch Exception e
                  (warn (str "error executing C++ compiler."))
                  (warn (str "" (.getMessage e)))
                  (io/exit-failure)))]
      (if (not= 0 (:exit ret))
        (do (warn "build error")
            (warn (:err ret))
            (io/exit-failure)))
      true)))
(defn clang-format [options]
  (let [file (cpp-file-name options)
        source (try (with-sh-dir "./"
                      (sh "clang-format" "-style" "{Standard: Cpp11}" file))
                    (catch Exception e nil))]
    (if source
      (do (info "formatting code")
          (io/write-to-file file (:out source))))))

(defn build-solution [spec-fn]
  (let [{:keys [input-file compile-program format-code path]} (spec-fn)]
    (info "dir =>" path)
    (info "file =>" input-file)

    (compile->cpp (read-clojure-file input-file) (spec-fn))

    (when format-code
      (clang-format (spec-fn)))

    (when compile-program
      (compile->binary (spec-fn)))))
(def program-options
  [["-i" "--input FILE"         "Input File" :default "./core.clj"]
   ["-o" "--output FILE"        "Output C++ File"]
   ["-b" "--binary FILE"        "Output Binary File"]
   ["-c" "--compile"            "Compile to Binary"]
   [nil  "--deps"               "Checkout Input Dependencies"]
   ["-w" "--watch-input"        "Automatically Recompile Input File on Change"]
   [nil  "--release"            "Compile in Release Mode. Strip Debug Information"]
   [nil  "--disable-formatting" "Disables Output File Formatting Using clang-format"]
   [nil  "--global-functions"   "Disables inline-global-fns Optimization"]
   [nil  "--ast"                "Print Intermediate AST"]
   [nil  "--silent"             "Silent or quiet mode"]
   ["-h" "--help"               "Print Help"]])
(defn -main [& args]
  (try
    (let [args (parse-opts args program-options)
          {:keys [help input deps watch-input silent]} (:options args)]

      (when help
        (try
          (let [version (io/read-file "build.info")]
            (print "ferret-lisp" version))
          (catch Exception e
            (print "ferret-lisp")))
        (println )
        (println )
        (println (:summary args))
        (io/exit-success))

      (when silent
        (System/setProperty "org.slf4j.simpleLogger.defaultLogLevel" "warn"))

      (when (not (io/file-exists input))
        (warn "no input file")
        (io/exit-failure))

      (let [specs (build-specs input args)]

        (when deps
          (try
            (checkout-deps (:path (specs)))
            (catch Exception e
              (io/exit-failure)))
          (io/exit-success))

        (if (not watch-input)
          (build-solution specs)
          (do (watcher/watcher [input]
                               (watcher/rate 1000)
                               (watcher/on-change
                                (fn [_] (build-solution specs))))
              @(promise)))
        (shutdown-agents))
      (io/exit-success))
    (catch Exception e
      (stacktrace/print-stack-trace e 10))))
