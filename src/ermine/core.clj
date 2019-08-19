(ns ermine.core
  (:refer-clojure :exclude [compile])
  (:use [clojure.java.io])
  (:import (java.io BufferedReader InputStreamReader)
           (org.apache.commons.io FilenameUtils FileUtils)
           (org.apache.commons.lang StringEscapeUtils)
           (org.antlr.stringtemplate StringTemplateGroup StringTemplate))
  (:require [clojure.set :as set]
            [flatland.ordered.map :as ordered-map]
            [fast-zip.core :as zip]
            [clojure.walk :as walk]
            [clojure.stacktrace :as stacktrace]
            [clojure.pprint :as pprint]
            [clojure.tools.cli :refer [parse-opts]]))

(defn create-view
  ([]
   (StringTemplate.))
  ([^String template]
   (StringTemplate. template)))

(defn stringify [any]
  (if (keyword? any)
    (name any)
    (str any)))

(declare kv-to-sv)
(declare scan-kv-to-sv)

(defn each-kv-to-sv [each]
  (if (map? each)
    (kv-to-sv each)
    (if (or (vector? each) (list? each) (seq? each) (set? each))
      (scan-kv-to-sv each)
      each)))

(defn scan-kv-to-sv [coll]
  (map each-kv-to-sv coll))

(defn kv-to-sv [mp]
  (let [m (into {} mp)
        k (keys m)
        v (vals m)]
    (zipmap
     (map stringify k)
     (scan-kv-to-sv v))))

(defn get-view-from-classpath [^String view-name]
  (let [st-group (StringTemplateGroup. "default")]
    (.getInstanceOf st-group view-name)))

(defn get-view-from-dir [^String view-name ^String root-dir]
  (let [st-group (StringTemplateGroup. "default" root-dir)]
    (.getInstanceOf st-group view-name)))

(defn reset-view! [^StringTemplate view ^String template]
  (.setTemplate view template))

(defn fill-view!
  ([^StringTemplate template k v]
    (.setAttribute template (stringify k) (each-kv-to-sv v))
    template)
  ([^StringTemplate template kv-map]
    (.setAttributes template (kv-to-sv kv-map))
    template))

(defn render-view [^StringTemplate template]
  (.toString template))

(defmacro render-template [template & vars]
  `(let [vars# (hash-map ~@vars)
         view# (create-view ~template)]
     (doseq [[k# v#] vars#]
       (fill-view! view# (name k#) v#))
     (render-view view#)))

(def extension-cpp "cpp")

(defn exit-failure []
  (System/exit 1))

(defn exit-success []
  (System/exit 0))

(defn read-file [f & [options]]
  (try
    (with-open [in (.getResourceAsStream (ClassLoader/getSystemClassLoader) f)
                rdr (BufferedReader. (InputStreamReader. in))]
      (apply str (interpose \newline (line-seq rdr))))
    (catch Exception _
      (try
        (if (nil? options)
          (FileUtils/readFileToString (file f))
          (FileUtils/readFileToString (file (str (:path options) f))))
        (catch Exception _
          #_(warn "error reading =>" f)
          (exit-failure))))))

(defn write-to-file [f s]
  (FileUtils/writeStringToFile (file f) (.trim s)))

(defn escape-string [s]
  (StringEscapeUtils/escapeJava s))

(defn file-path [file]
  (let [path (str (FilenameUtils/getPrefix file) (FilenameUtils/getPath file))]
    (if (empty? path) "./" path)))

(defn file-extension [f]
  (FilenameUtils/getExtension f))

(defn file-base-name [f]
  (FilenameUtils/getBaseName f))

(defn file-exists [f]
  (.exists (file f)))

(defn make-file [p n e]
  (file (str p n "." e)))

(defn form?
  ([s]
   #(form? s %))
  ([s f]
   (and (seq? f)
        (= (first f) s))))

(defn symbol-set [form]
  (->> form flatten (filter symbol?) (into #{})))

(defn split-fn [sig]
  (let [name (if (symbol? (second sig)) (second sig) nil)
        sig  (if name (drop 2 sig) (rest sig))
        [args & body] sig]
    [name args body]))

(defn ffi-fn? [body]
  (and (not (nil? body))
       (not (empty? body))
       (->> (map string? body)
            (every? true?))))

(defn fn-arg-symbol? [s]
  (and (symbol? s)
       (not= s '&)
       (not= s '_)
       (not= s 'fir-destructure-associative)))

(defn transform [tree pred f]
  (walk/prewalk (fn [form]
                  (if (pred form)
                    (let [new-form (f form)
                          meta (meta form)]
                      (if (and (instance? clojure.lang.IMeta form)
                               (instance? clojure.lang.IMeta new-form))
                        (with-meta new-form meta)
                        new-form))
                    form))
                tree))

(defn parser-drop [tree pred]
  (if (every? true? (map #(pred %) tree))
    (list )
    (loop [loc (zip/seq-zip tree)]
      (if (zip/end? loc)
        (zip/root loc)
        (recur
         (zip/next
          (if (pred (zip/node loc))
            (zip/remove loc)
            loc)))))))

(defn parser-peek [tree pred & [node-fn]]
  (let [node-fn (if node-fn
                  node-fn
                  #(zip/node %))]
    (loop [loc (zip/seq-zip tree)
           nodes []]
      (if (zip/end? loc)
        nodes
        (recur
         (zip/next loc)
         (if (pred (zip/node loc))
           (conj nodes (node-fn loc))
           nodes))))))

(defn new-symbol [& parts]
  (let [parts (map #(.replace (str %) "." "_") parts)]
    (symbol (apply str parts))))

(defn fn-make-unique [args body]
  (if (string?  (->> body
                     (filter #(not (form? 'native-declare %)))
                     first))
    [args body]
    (let [unique-args (->> args
                           flatten
                           (filter fn-arg-symbol?)
                           (map #(new-symbol % (gensym "__"))))
          replace? (->> (interleave (->> args
                                         flatten
                                         (filter fn-arg-symbol?))
                                    unique-args)
                        (apply hash-map))
          body      (transform body #(replace? %) #(replace? %))
          replace?  (merge replace? {'fir-new-map 'fir-destructure-associative})
          args      (transform args #(replace? %) #(replace? %))]
      [args body])))

(defn new-fir-fn
  ([& {:keys [name args body escape] :or {escape  true
                                          args    []}}]
   (let [name-unique (if name
                       (new-symbol name (gensym "__")))
         [args body] (if escape
                       (fn-make-unique args body)
                       [args body])
         body        (if name-unique
                       (transform body #(= % name) (fn [_] name-unique))
                       body)]
     (if name-unique
       `(fn* ~name-unique ~args ~@body)
       `(fn* ~args ~@body)))))

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
      (-> (read-string (str \( (read-file f) \)))
          (transform
           symbol?
           #(if (= (namespace %) ns-str)
              (-> % name symbol)
              %))
          ;;replace clojure.core/fn with fn
          ;;replace clojure.core/while with while
          (transform
           (fn [x]
             (and (form? 'quote x)
                  (or (= 'clojure.core/fn    (second x))
                      (= 'clojure.core/defn  (second x))
                      (= 'clojure.core/while (second x)))))
           (fn [[_ s]] `'~(-> s name symbol)))))))

(defn expand-reader-macros [form]
  (-> form
      (transform
       (form? 'clojure.core/deref)
       (fn [f] (cons 'deref (rest f))))
      (transform
       map?
       (fn [x]
         (->> (seq x)
              (reduce
               (fn[h [k v]]
                 (conj h k v)) [])
              (seq)
              (cons 'fir-new-map))))))

(defn macro-normalize [f]
  (transform f
                    (form? 'let)
                    (fn [[_ bindings & body]]
                      `(~'let* ~(apply list bindings) ~@body))))

(defn expand-macros-single [form]
  (let [core-macros (->> (read-clojure-file "ermine/lang.clj")
                         (filter (form? 'defmacro)))
        core-macro-symbols (into #{} (map second core-macros))
        form-macros (->> (filter (form? 'defmacro) form)
                         (filter (fn [[_ name]]
                                   (not (core-macro-symbols name)))))
        form-macro-symbols (map second form-macros)
        form (parser-drop form (form? 'defmacro))
        temp-ns (gensym)
        macro-symbols (concat core-macro-symbols form-macro-symbols)]

    (create-ns temp-ns)
    (binding [*ns* (the-ns temp-ns)]
      (refer 'clojure.core :exclude (concat macro-symbols ['fn 'def]))
      (use '[ermine.core :only [exit-failure new-fir-fn symbol-conversion]])

      (doseq [m (concat core-macros form-macros)]
        (eval m)))

    (let [form (-> form
                   (macro-normalize)
                   (expand-reader-macros)
                   (transform
                    (fn [f]
                      (some true? (map #(form? % f) macro-symbols)))
                    (fn [f]
                      (binding [*ns* (the-ns temp-ns)]
                        (-> (walk/macroexpand-all f)
                            ;;strip ns from symbols
                            (transform symbol? #(-> % name symbol)))))))]
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
                      (or (form? 'defn f)
                          (form? 'defnative f)))
         header-symbols (->> (parser-peek header seq?)
                             (symbol-set))
         header-fns (->> (parser-peek header shakeable?)
                         (map #(vector (second %) %))
                         (into {}))
         header-non-shakeable (parser-drop header shakeable?)
         form-expanded (expand-macros (concat header-non-shakeable form))
         fns (atom #{})
         _ (shake-concat form-expanded header-fns fns header-non-shakeable)
         header-shaked (parser-drop header (fn [f]
                                             (and (shakeable? f)
                                                  (not (@fns (second f))))))]
     (concat header-shaked form)))
  ([form built-in fns non-shakeable]
   (transform form symbol?
                     #(do
                        (if-let [f (built-in %)]
                          (when (not (@fns %))
                            (swap! fns conj %)
                            (shake-concat (expand-macros (concat non-shakeable f))
                                          built-in fns non-shakeable))) %))))

(defn escape-fn-calls [form]
  (let [arity (parser-peek
               form
               (fn [f]
                 (and (form? 'fir-defn-heap f)
                      (-> (parser-peek f (form? 'fir-defn-arity))
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
        (transform
         (form? 'fir-defn-arity)
         (fn [f]
           (transform f
                             (form? 'fir-fn-heap)
                             (fn [[_ & f]]
                               `(~'fir-fn-stack ~@f)))))
        (transform
         (fn [f]
           (and (seq? f)
                (form? 'fir-fn-heap (first f))
                (arity (-> f first second))))
         (fn [f]
           (let [[[_ fn] & args] f
                 dispatch ((arity fn) (count args))
                 default  ((arity fn) :default)]
             (cond dispatch `((~'fir-fn-heap ~dispatch) ~@args)
                   default  `((~'fir-fn-heap ~default)  ~@args)
                   :default f))))
        (transform
         (fn [f]
           (and (symbol? f)
                (arity-renames f)))
         (fn [f]
           (arity-renames f)))
        ;; resolve fn calls
        (transform
         (fn [f]
           (and (seq? f)
                (form? 'fir-fn-heap (first f))))
         (fn [f]
           (let [[[_ & fn] & args] f]
             `((~'fir-fn-stack ~@fn) ~@args)))))))

(defn escape-fn-inheritance [form]
  (let [heap-fns (->> (parser-peek form (form? 'fir-fn-heap))
                      (map second)
                      (into #{}))
        stack-fns (->> (parser-peek form (form? 'fir-fn-stack))
                       (map second)
                       (into #{}))
        escapeable-fns (set/difference stack-fns heap-fns)]
    (transform form
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
    (->> (parser-peek form (form? 'require))
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
                                          (parser-drop (form? 'configure-runtime!))
                                          (parser-drop (form? 'configure-ermine!)))
                       macro-symbols  (->> (parser-peek mod (form? 'defmacro))
                                           (map second)
                                           (into #{}))
                       def-symbols    (->> (parser-peek (expand-macros mod) (form? 'def))
                                           (map second)
                                           (into #{}))
                       replace?       (set/union macro-symbols def-symbols)
                       mod            (transform
                                       mod
                                       #(and (symbol? %)
                                             (replace? %))
                                       #(new-symbol m "_" %))]
                   (reduce (fn [h v] (conj h v)) h mod)))
               [])
       lazy-seq))

(defn import-modules-convert-alias-to-module [package-list form]
  (let [alias-to-mod (reduce (fn[h [mod aliases]]
                               (reduce (fn[h v] (assoc h v mod)) h aliases))
                             {} package-list)]
    (transform form symbol?
                      (fn [f]
                        (if-let [[_ alias fn] (re-find #"(.*?)/(.*)" (str f))]
                          (if-let [mod-sym (alias-to-mod (symbol alias))]
                            (new-symbol mod-sym "_" fn)
                            f)
                          f)))))

(defn import-modules [form options]
  (let [package-list (import-modules-select-require form)
        form         (parser-drop form (form? 'require))
        modules      (import-modules-load-modules package-list options)
        non-public?  (->> modules
                          (reduce (fn[private-symbols mod]
                                    (-> mod
                                        (parser-peek #(and (symbol? %)
                                                           (-> % meta :private)))
                                        (concat private-symbols))) [])
                          (into #{}))
        form         (import-modules-convert-alias-to-module package-list form)
        violations   (parser-peek form #(non-public? %) #(zip/node (zip/up %)))]
    (when (not (empty? violations))
      (doseq [v violations]
        #_(warn "non-public-access =>" v))
      (exit-failure))
    (shake-concat modules form)))

(defn import-modules-all [form options]
  (loop [f form]
    (let [expanded (import-modules f options)]
      (if (= f expanded)
        expanded
        (recur expanded)))))

(defn ermine-runtime [options form]
  (->> (-> form
           (import-modules-all options)
           (expand-reader-macros))
       (shake-concat (read-clojure-file "ermine/lang.clj"))
       (cons `(~'native-define ~(str "// ermine-lisp")))))

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
    #_(warn
     (str "let requires an even number of forms in binding vector => " bindings))
    (exit-failure)))

(defn let->fn [form]
  (-> form

      (transform (form? 'let*)
                        (fn [[_ bindings & body]]
                          (let-assert bindings body)
                          (let-closure bindings body)))

      (transform (form? 'fir-let-fn)
                        (fn [[_ args & body]]
                          (new-fir-fn :args args :body body)))))

(defn do->fn [form]
  (transform form
                    (form? 'do)
                    (fn [f] `(~(new-fir-fn :body (rest f))))))

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
   (transform
    form
    (form? 'fn*)
    (fn [sig]
      (let [[name args body] (split-fn sig)
            ;; transform named recursion in body
            body (if name
                   (transform
                    body
                    (form? name)
                    (fn [[_ & args]]
                      (cons
                       (apply list 'fir-fn-heap name env)
                       args)))
                   body)
            body (fn->lift body fns (concat args env))
            symbols (symbol-set body)
            env  (->> (set/intersection
                       symbols
                       (into #{} (flatten env)))
                      (into ()))

            args (if (ffi-fn?
                      (filter #(not (form? 'native-declare %)) body))
                   args
                   (transform args
                                     symbol?
                                     (fn [v]
                                       (if (or (not (fn-arg-symbol? v))
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
    (transform form symbol? c)))

(defn inline-defn? [f]
  (and (form? 'def f)
       (-> f second meta :tag (not= 'volatile))
       (form? 'fir-fn-heap
                     (->> f (drop 2) first))))

(defn fn->inline [options form]
  (if (:global-functions options)
    form
    (let [defns      (->> (parser-peek form inline-defn?)
                          (filter #(= 2 (-> % last count))))
          fn-table   (map (fn [[_ name [_ gensym]]] [name gensym]) defns)
          impl-table (apply hash-map (flatten fn-table))
          defn?      (fn [f]
                       (and (inline-defn? f)
                            (impl-table (second f))))
          invoke     #(if-let [imp (impl-table %)]
                        (list 'fir-fn-heap imp)
                        %)
          no-defn    (reduce (fn[h v] (parser-drop h defn?)) form defns)
          inlined    (reduce (fn[h [name gensym]]
                               (transform h
                                                 #(or (form? name %)
                                                      (form? 'def %))
                                                 (fn [f] (map invoke f))))
                             no-defn fn-table)]
      (reduce (fn[h [name gensym]]
                (transform h #(and (symbol? %)
                                          (= % gensym))
                                  (fn [_] (identity name))))
              inlined fn-table))))

(defn escape-analysis [form]
  (->> form
       (escape-fn-calls)
       (escape-fn-inheritance)))

(defn compile [form options]
  (->> (ermine-runtime options form)
       (expand-macros)
       (let->fn)
       (do->fn)
       (fn->lift)
       (fn->inline options)
       (escape-analysis)
       (symbol-conversion)))

(defmulti emit (fn [_ f _]
                 (cond (form? '(fir_fn_stack list) f)   'fir_inline_list
                       (form? '(fir_fn_stack first) f)  'fir_inline_first
                       (form? '(fir_fn_stack rest) f)   'fir_inline_rest
                       (form? 'fir_defn_heap f)   'fir_defn_heap
                       (form? 'fir_defn_stack f)  'fir_defn_stack
                       (form? 'fir_defn_arity f)  'fir_defn_arity
                       (form? 'fir_fn_heap f)     'fir_fn_heap
                       (form? 'fir_fn_stack f)    'fir_fn_stack
                       (form? 'list f)            'list
                       (form? 'defobject f)       'defobject
                       (form? 'native_header f)   'native_header
                       (form? 'native_declare f)  'native_declare
                       (form? 'native_define f)   'native_define
                       (form? 'if f)              'if
                       (form? 'def f)             'def
                       (form? 'fir_new_map f)     'fir_new_map
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
  #_(warn "unsupported form =>" form)
  (exit-failure))

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
  (str "obj<string>(\"" (escape-string form) "\"," (count form) ")"))

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
        (StringEscapeUtils/unescapeJava
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

(defn defobject [name spec options]
  (render-template
   "#ifndef ERMINE_OBJECT_$guard$
    #define ERMINE_OBJECT_$guard$
     $body$
    #endif"
   :guard       (.toUpperCase (str name))
   :body        (first spec)))

(defmethod emit 'list [options [fn & args] state]
  (let [elements  (->> (emit-ast options args state)
                       (interpose \,)
                       (apply str))]
    (str "rt::list(" elements ")")))

(defmethod emit 'defobject [options [_ name & spec] state]
  (append-to! state [:objects] (defobject name spec options)))

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

                  (form? 'fir_destructure_associative name)
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
         args-indexed   (->> args (map-indexed (fn [p v] [p v])) (filter #(not= (second %) '_)))
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
  (let [native-declarations (filter (form? 'native_declare) body)
        return (fn [b] (conj (pop b) (str "return " (last b))))
        body (filter #(not (form? 'native_declare %)) body)
        body (cond  (empty? body)
                    ["return nil()"]
                    ;; multi arity dispacth
                    (form? 'fir_defn_arity (first body))
                    (return
                     (emit options (first body) state))
                    ;; ffi call
                    (ffi-fn? body)
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
                        "
#if !defined(ERMINE_DISABLE_STD_MAIN)
 #if defined(ERMINE_DISABLE_CLI_ARGS) || !defined(ERMINE_STD_LIB)
  int main()
 #else
  int main(int argc, char* argv[])
 #endif
  {     
    using namespace ermine;
    ERMINE_ALLOCATOR::init();
    rt::init();

   #if defined(ERMINE_STD_LIB) && !defined(ERMINE_DISABLE_CLI_ARGS)
    for (int i = argc - 1; i > -1 ; i--)
      _star_command_line_args_star_ =  rt::cons(obj<string>(argv[i]),_star_command_line_args_star_);
   #endif

    $file$::main();

   #if defined(ERMINE_PROGRAM_MAIN)
    run(ERMINE_PROGRAM_MAIN);
   #endif

    return 0;
  }
#endif
"
                        :file       file-ns)]
    (render-template
     "
        $native_defines:{$it$} ;separator=\"\n\"$
        $native_headers:{#include \"$it$\"} ;separator=\"\n\"$

        #ifndef ERMINE_RUNTIME_H
        #define ERMINE_RUNTIME_H
         $ermine_h$
        #endif

        // Objects
        namespace ermine{
         $objects:{$it$} ;separator=\"\n\"$
        }

        // Symbols
        namespace $file${
         using namespace ermine;

         $symbols:{var $it$;} ;separator=\"\n\"$
        }

        $native_declarations:{$it$} ;separator=\"\n\"$

        // Runtime Implementations
        #ifndef ERMINE_RUNTIME_CPP
        #define ERMINE_RUNTIME_CPP
         $ermine_cpp$
        #endif

        // Lambda Prototypes
        namespace $file${
          $lambda_classes:{$it$} ;separator=\"\n\"$
        }

        // Command Line Arguments
        #if defined(ERMINE_STD_LIB) && !defined(ERMINE_DISABLE_CLI_ARGS) && !defined(ERMINE_DISABLE_STD_MAIN)
          ermine::var _star_command_line_args_star_;
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

        $ermine_main$"
     :file                 file-ns
     :native_defines       native-defines
     :ermine_h             "
// Detect Hardware
# define ERMINE_CONFIG_SAFE_MODE TRUE

#if !defined(ERMINE_SAFE_MODE)
  #if defined(__APPLE__) || defined(_WIN32) || defined(__linux__) || defined(__unix__) || defined(_POSIX_VERSION)

    # undef  ERMINE_CONFIG_SAFE_MODE
    # define ERMINE_STD_LIB TRUE
  #endif
#endif

#if defined(ERMINE_CONFIG_SAFE_MODE)
  # define ERMINE_DISABLE_MULTI_THREADING TRUE
  # define ERMINE_DISABLE_STD_OUT TRUE
#endif

#ifdef ERMINE_STD_LIB
 #include <iostream>
 #include <iomanip>
 #include <sstream>
 #include <cstdio>
 #include <cstdlib>
 #include <cstddef>
 #include <cmath>
 #include <vector>
 #include <algorithm>
 #include <chrono>
 #include <atomic>
 #include <mutex>
 #include <thread>
 #include <future>
#endif

#ifdef ERMINE_CONFIG_SAFE_MODE
 #include <stdio.h>
 #include <stdlib.h>
 #include <stdint.h>
 #include <math.h>
#endif

namespace ermine{
  namespace runtime {}
  namespace rt = runtime;
  // Types
  typedef uint8_t byte;
  #pragma pack(push, 1)
  class int24_t {
  protected:
    byte word[3];
  public:
    int24_t(){ }
  
    template<typename T>
    explicit int24_t( T const & val ) {
      *this   = (int32_t)val;
    }
  
    int24_t( const int24_t& val ) {
      *this   = val;
    }
  
    operator int32_t() const {
      if (word[2] & 0x80) { // negative? - then sign extend.
        return
          (int32_t)(((uint32_t)0xff    << 24) |
                    ((uint32_t)word[2] << 16) |
                    ((uint32_t)word[1] << 8)  |
                    ((uint32_t)word[0] << 0));
      }else{
        return
          (int32_t)(((uint32_t)word[2] << 16) |
                    ((uint32_t)word[1] << 8)  |
                    ((uint32_t)word[0] << 0));
      }
    }
  
    int24_t& operator =( const int24_t& input ) {
      word[0]   = input.word[0];
      word[1]   = input.word[1];
      word[2]   = input.word[2];
  
      return *this;
    }
  
    int24_t& operator =( const int32_t input ) {
      word[0]   = ((byte*)&input)[0];
      word[1]   = ((byte*)&input)[1];
      word[2]   = ((byte*)&input)[2];
  
      return *this;
    }
  
    int24_t operator +( const int24_t& val ) const {
      return int24_t( (int32_t)*this + (int32_t)val );
    }
  
    int24_t operator -( const int24_t& val ) const {
      return int24_t( (int32_t)*this - (int32_t)val );
    }
  
    int24_t operator *( const int24_t& val ) const {
      return int24_t( (int32_t)*this * (int32_t)val );
    }
  
    int24_t operator /( const int24_t& val ) const {
      return int24_t( (int32_t)*this / (int32_t)val );
    }
  
    int24_t& operator +=( const int24_t& val ) {
      *this   = *this + val;
      return *this;
    }
  
    int24_t& operator -=( const int24_t& val ) {
      *this   = *this - val;
      return *this;
    }
  
    int24_t& operator *=( const int24_t& val ) {
      *this   = *this * val;
      return *this;
    }
  
    int24_t& operator /=( const int24_t& val ) {
      *this   = *this / val;
      return *this;
    }
  
    int24_t operator -() {
      return int24_t( -(int32_t)*this );
    }
  
    bool operator ==( const int24_t& val ) const {
      return (int32_t)*this == (int32_t)val;
    }
  
    bool operator !=( const int24_t& val ) const {
      return (int32_t)*this != (int32_t)val;
    }
  
    bool operator >=( const int24_t& val ) const {
      return (int32_t)*this >= (int32_t)val;
    }
  
    bool operator <=( const int24_t& val ) const {
      return (int32_t)*this <= (int32_t)val;
    }
  
    bool operator >( const int24_t& val ) const {
      return (int32_t)*this > (int32_t)val;
    }
  
    bool operator <( const int24_t& val ) const {
      return (int32_t)*this < (int32_t)val;
    }
  };
  #pragma pack(pop)
  // Concurrency
  #if defined(ERMINE_DISABLE_MULTI_THREADING)
    class mutex {
    public:
      void lock()   {} 
      void unlock() {} 
    };
  #else
    #if defined(ERMINE_STD_LIB)
      class mutex {
        ::std::mutex m;
      public:
        void lock()   { m.lock();   } 
        void unlock() { m.unlock(); }
      };
    #endif
  #endif
  
  class lock_guard{
    mutex & _ref;
  public:
    explicit lock_guard(const lock_guard &) = delete;
    explicit lock_guard(mutex & mutex) : _ref(mutex) { _ref.lock(); };
    ~lock_guard() { _ref.unlock(); }
  };
  // Containers
  #undef bit
  
  #if !defined(ERMINE_BITSET_WORD_TYPE)
    #define ERMINE_BITSET_WORD_TYPE unsigned int
    #if defined(__clang__) || defined(__GNUG__)
      #define ERMINE_BITSET_USE_COMPILER_INTRINSICS true
    #endif
  #endif
  
  template<size_t S, typename word_t = ERMINE_BITSET_WORD_TYPE>
  class bitset {
    static const size_t bits_per_word = sizeof(word_t) * 8;
    static const size_t n_words = S / bits_per_word;
  
    static_assert((S % bits_per_word) == 0, \"bitset size must be a multiple of word_t\");
  
    word_t bits[n_words];
  
    inline size_t word (size_t i) const { return i / bits_per_word; }
    inline size_t bit  (size_t i) const { return i % bits_per_word; }
  
  public:
    bitset() : bits{ word_t(0x00) } { }
  
    inline void set   (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] |  (word_t(1) << (bit(b))));
    }
  
    inline void set (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline void reset (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] & ~(word_t(1) << (bit(b))));
    }
  
    inline void reset (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline void flip (size_t b){
      bits[word(b)] = (word_t)(bits[word(b)] ^  (word_t(1) << (bit(b))));
    }
  
    inline void flip (size_t b, size_t e){
      size_t word_ptr = word(b);
      size_t n_bits = e - b;
  
      bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(bit(b), n_bits));
  
      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for (; word_ptr < last_word; word_ptr++){
        bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }
  
    inline bool test  (size_t b) const {
      return (bits[word(b)] & (word_t(1) << (bit(b))));
    }
  
    inline size_t ffs(size_t b = 0, size_t e = S) const {
  #if defined(ERMINE_BITSET_USE_COMPILER_INTRINSICS)
        // search first word
        size_t word_ptr = word(b);
        word_t this_word = bits[word_ptr];
  
        // mask off bits below bound
        this_word &= (~static_cast<word_t>(0)) << bit(b);
        
        if (this_word != static_cast<word_t>(0))
  	return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
  
        // check subsequent words
        word_ptr++;
        size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
        for (; word_ptr < last_word; word_ptr++){
          this_word = bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for(size_t i = b; i < e; i++)
          if (test(i))
            return i;
  #endif
      return S;
    }
  
    inline size_t ffr(size_t b = 0, size_t e = S) const {
  #if defined(ERMINE_BITSET_USE_COMPILER_INTRINSICS)
        // same as ffs but complements word before counting
        size_t word_ptr = word(b);
        word_t this_word = ~bits[word_ptr];
  
        this_word &= (~static_cast<word_t>(0)) << bit(b);
        
        if (this_word != static_cast<word_t>(0))
  	return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
  
        word_ptr++;
        size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
        for (; word_ptr < last_word; word_ptr++){
          this_word = ~bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for(size_t i = b; i < e; i++)
          if (!test(i))
            return i;
  #endif
      return S;
    }
  
    // Return word with length-n bit block starting at bit p set.
    // Both p and n are effectively taken modulo bits_per_word.
    static inline word_t bit_block(size_t p, size_t n){
      if (n >= bits_per_word)
        return (word_t)(word_t(-1) << p);
  
      word_t x = (word_t)((word_t(1) << n) - word_t(1));
      return  (word_t)(x << p);
    }
  
  #if defined(ERMINE_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, bitset& x) {
      for(size_t i = 0; i < S; i++)
        stream << x.test(i);
      return stream;
    }
  #endif
  };
}

// Math
namespace ermine{
  constexpr auto operator \"\" _MB( unsigned long long const x ) -> long {
    return 1024L * 1024L * (long)x;
  }
  
  constexpr auto operator \"\" _KB( unsigned long long const x ) -> long {
    return 1024L * (long)x;
  }
  
  constexpr auto operator \"\" _pi(long double x) -> double {
    return 3.14159265358979323846 * (double)x;
  }
  
  constexpr auto operator \"\" _pi(unsigned long long int  x) -> double {
    return 1.0_pi * (double)x;
  }
  
  constexpr auto operator \"\" _deg(long double x) -> double {
    return (1.0_pi * (double)x) / 180;
  }
  
  constexpr auto operator \"\" _deg(unsigned long long int  x) -> double {
    return 1.0_deg * (double)x;
  }
  #if !defined(__clang__)
  constexpr auto operator \"\" _QN(long double x) -> int {
    return (int)::floor(::log(1.0/(double)x)/::log(2));
  }
  #endif
  
  template<int bits> struct fixed_real_container;
  template<> struct fixed_real_container<8>  { typedef int8_t  base_type;
                                               typedef int16_t next_type; };
  template<> struct fixed_real_container<16> { typedef int16_t base_type;
                                               typedef int24_t next_type; };
  template<> struct fixed_real_container<24> { typedef int24_t base_type;
                                               typedef int32_t next_type; };
  template<> struct fixed_real_container<32> { typedef int32_t base_type;
                                               typedef int64_t next_type; };
  template<> struct fixed_real_container<64> { typedef int64_t base_type;
                                               typedef int64_t next_type; };
  
  #pragma pack(push, 1)
  template<int bits, int exp>
  class fixed_real {
    typedef fixed_real fixed;
    typedef typename fixed_real_container<bits>::base_type base;
    typedef typename fixed_real_container<bits>::next_type next;
  
    base m;
    static const int N      = (exp - 1);
    static const int factor = 1 << N;
  
    template<typename T>
    inline base from(T d) const { return (base)(d * factor); }
  
    template<typename T>
    inline T to_rational() const { return T(m) / factor; }
  
    template<typename T>
    inline T to_whole() const { return (T)(m >> N); }
  
  public:
  
    //from types
    explicit fixed_real( )           : m(0) { }
    template<typename T>
    explicit fixed_real(T v)         : m(from<T>(v)) {}
  
    template<typename T>
    fixed& operator=(T v)        { m = from<T>(v); return *this; }
  
    //to types
    template<typename T>
    operator T()           const { return to_whole<T>();    }
    operator double()      const { return to_rational<double>(); }
  
    // operations
    fixed& operator+= (const fixed& x) { m += x.m; return *this; }
    fixed& operator-= (const fixed& x) { m -= x.m; return *this; }
    fixed& operator*= (const fixed& x) { m = (base)(((next)m * (next)x.m) >> N); return *this; }
    fixed& operator/= (const fixed& x) { m = (base)(((next)m * factor) / x.m); return *this; }
    fixed& operator*= (int x)          { m *= x; return *this; }
    fixed& operator/= (int x)          { m /= x; return *this; }
    fixed  operator-  ( )              { return fixed(-m); }
  
    // friend functions
    friend fixed operator+ (fixed x, const fixed& y) { return x += y; }
    friend fixed operator- (fixed x, const fixed& y) { return x -= y; }
    friend fixed operator* (fixed x, const fixed& y) { return x *= y; }
    friend fixed operator/ (fixed x, const fixed& y) { return x /= y; }
  
    // comparison operators
    friend bool operator== (const fixed& x, const fixed& y) { return x.m == y.m; }
    friend bool operator!= (const fixed& x, const fixed& y) { return x.m != y.m; }
    friend bool operator>  (const fixed& x, const fixed& y) { return x.m > y.m; }
    friend bool operator<  (const fixed& x, const fixed& y) { return x.m < y.m; }
    friend bool operator>= (const fixed& x, const fixed& y) { return x.m >= y.m; }
    friend bool operator<= (const fixed& x, const fixed& y) { return x.m <= y.m; }
  
  #if defined(ERMINE_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, const fixed& x) {
      stream << (double)x;
      return stream;
    }
  #endif
  };
  #pragma pack(pop)
  #if !defined(ERMINE_NUMBER_TYPE)
     #define ERMINE_NUMBER_TYPE int
  #endif
  
  #if !defined(ERMINE_REAL_TYPE)
     #define ERMINE_REAL_TYPE   double
  #endif
  
  #if !defined(ERMINE_REAL_EPSILON)
     #define ERMINE_REAL_EPSILON   0.0001
  #endif
  
    int req_real_precision(double t) {
      return ((-1 * (int)log10(t)));
    }
  
    typedef ERMINE_NUMBER_TYPE  number_t;                   // Whole number Container.
    typedef ERMINE_REAL_TYPE    real_t;                     // Real number Container.
    const   real_t              real_epsilon(ERMINE_REAL_EPSILON);
    const   int                 real_precision = req_real_precision(ERMINE_REAL_EPSILON);
  namespace runtime{
    #undef min
    #undef max
    #undef abs
  
    template <typename T>
    static constexpr T max(T a, T b) {
      return a < b ? b : a;
    }
  
    template <typename T, typename... Ts>
    static constexpr T max(T a, Ts... bs) {
      return max(a, max(bs...));
    }
  
    template<typename T>
    constexpr T min(T a, T b){
      return ((a) < (b) ? (a) : (b));
    }
  
    template <typename T, typename... Ts>
    static constexpr T min(T a, Ts... bs) {
      return min(a, min(bs...));
    }
  
    template<typename T>
    constexpr T abs(T a){
      return ((a) < (T)0 ? -(a) : (a));
    }
  }
}

// Initialize Hardware
namespace ermine{
  #if !defined(ERMINE_UART_RATE)
    # define ERMINE_UART_RATE 9600
  #endif
  #if !defined(ERMINE_IO_STREAM_SIZE)
    # define ERMINE_IO_STREAM_SIZE 80
  #endif
  #if defined(ERMINE_DISABLE_STD_OUT)
     namespace runtime{
       void init(){ }
  
       template <typename T>
       void print(T){ }
     }
  #endif
  #if defined(ERMINE_STD_LIB) && !defined(ERMINE_DISABLE_STD_OUT)
    namespace runtime{
      void init(){}
  
      template <typename T>
      void print(const T & t){ std::cout << t; }
  
      template <>
      void print(const real_t & n){
        std::cout << std::fixed << std::setprecision(real_precision) << n;
      }
  
      void read_line(char *buff, std::streamsize len){
        std::cin.getline(buff, len);
      }
    }
  #endif
  #if !defined(ERMINE_DISABLE_STD_OUT)
     namespace runtime{
       template <typename T>
       void println(T t){
         print(t);
         print((char)0xA);
       }
     }
  #endif
}

// Object System Base
namespace ermine{
  namespace memory {
    template <typename T>
    class pointer{
      T *ptr;
  
    public:
  
      inline explicit pointer(T *p = nullptr) : ptr(p){ }
      inline operator T* () const { return ptr; }
  
      inline pointer& operator= (T *other){
        ptr = other;
        return *this;
      }
  
      inline T *operator->() const { return ptr; }
    };
  }
  namespace memory{
    inline size_t align_of(uintptr_t size, size_t align){
      return (size + align - 1) & ~(align - 1);
    }
  
    template<class T>
    size_t align_of(const void * ptr) {
      return align_of(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }
  
    inline size_t align_req(uintptr_t size, size_t align){
      size_t adjust = align - (size & (align - 1));
  
      if(adjust == align)
        return 0;
      return adjust;
    }
  
    template<class T>
    size_t align_req(const void * ptr) {
      return align_req(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }
  
    template <typename... Ts>
    constexpr size_t max_sizeof() {
      return rt::max(sizeof(Ts)...);
    }
  }
  #ifdef ERMINE_MEMORY_POOL_SIZE
  namespace memory{
    namespace allocator{
      template<typename page_t, size_t pool_size,
               typename bitset_word_t = ERMINE_BITSET_WORD_TYPE>
      struct memory_pool {
        bitset<pool_size, bitset_word_t> used;
        page_t pool[pool_size];
        size_t next_ptr;
  
        memory_pool() : pool{0}, next_ptr(0) { }
  
        inline size_t scan(size_t n_pages, size_t from_page = 0) const {
          for(;;){
            size_t begin = used.ffr(from_page);
            size_t end   = begin + n_pages;
  
            if (end > pool_size)
              return pool_size;
  
            if (used.ffs(begin, end) >= end)
              return begin;
  
            from_page = end;
          }
        }
  
        void *allocate(size_t req_size){
          req_size = align_of(req_size, sizeof(page_t)) + sizeof(page_t);
          size_t n_pages = req_size / sizeof(page_t);
          size_t page   = scan(n_pages, next_ptr);
  
          if (page == pool_size){
            page = scan(n_pages);
            if (page == pool_size)
              return nullptr;
          }
  
          pool[page] = (page_t)n_pages;
          next_ptr = page + n_pages;
          used.flip(page, next_ptr);
  
          return &pool[++page];
        }
  
        void free(void *p){
          ptrdiff_t begin = (static_cast<page_t *>(p) - pool) - 1;
          ptrdiff_t end = begin + (ptrdiff_t)pool[begin];
          used.flip((size_t)begin, (size_t)end);
        }
      };
    }
  }
  #endif
  #if defined(ERMINE_MEMORY_POOL_SIZE) && !defined(ERMINE_ALLOCATOR)
  
   #define ERMINE_ALLOCATOR memory::allocator::pool
  
   #if !defined(ERMINE_MEMORY_POOL_PAGE_TYPE)
    #define ERMINE_MEMORY_POOL_PAGE_TYPE size_t
   #endif
  
  namespace memory{
    namespace allocator{
  
      memory_pool<ERMINE_MEMORY_POOL_PAGE_TYPE, ERMINE_MEMORY_POOL_SIZE> program_memory;
  
      class pool{
      public:
  
        static void init(){ }
  
        static inline void*  allocate(size_t s){
          return program_memory.allocate(s);
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void   free(void * ptr){ program_memory.free(ptr); }
      };
    }
  }
  #endif
  #ifdef ERMINE_MEMORY_BOEHM_GC
  
  #define ERMINE_ALLOCATOR memory::allocator::gc
  #define ERMINE_DISABLE_RC true
  
  #include <gc.h>
  
  namespace memory{
    namespace allocator{
  
      class gc{
      public:
  
        static void init(){ GC_INIT(); }
  
        static inline void* allocate(size_t s){
  #ifdef ERMINE_DISABLE_MULTI_THREADING
          return GC_MALLOC(s);
  #else
          return GC_MALLOC_ATOMIC(s);
  #endif
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){ }
      };
    }
  }
  #endif
  #if !defined(ERMINE_ALLOCATOR)
  
  #define ERMINE_ALLOCATOR memory::allocator::system
  
  namespace memory{
    namespace allocator{
  
      class system{
      public:
  
        static void init(){ }
  
        static inline void* allocate(size_t s){ return ::malloc(s); }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){ ::free(ptr); } 
      };
    }
  }
  #endif
  namespace memory{
    namespace allocator{
      class synchronized{
        static mutex lock;
      public:
  
        static void init(){ ERMINE_ALLOCATOR::init(); }
  
        static inline void* allocate(size_t s){
          lock_guard guard(lock);
          return ERMINE_ALLOCATOR::allocate(s);
        }
  
        template<typename FT>
        static inline void* allocate(){ return allocate(sizeof(FT)); }
  
        static inline void  free(void * ptr){
          lock_guard guard(lock);
          ERMINE_ALLOCATOR::free(ptr);
        }
      };
    }
  }
  #if  !defined(ERMINE_DISABLE_MULTI_THREADING)
  
    #if defined(ERMINE_MEMORY_POOL_SIZE)
      mutex memory::allocator::synchronized::lock;
      #undef  ERMINE_ALLOCATOR
      #define ERMINE_ALLOCATOR memory::allocator::synchronized
    #endif
  
  #endif
  #if !defined(ERMINE_RC_POLICY)
  namespace memory {
    namespace gc {
  
  #if !defined(ERMINE_RC_TYPE)
    #define ERMINE_RC_TYPE unsigned int
  #endif
  
  #if defined(ERMINE_DISABLE_RC)
  
  #define ERMINE_RC_POLICY memory::gc::no_rc
  
      class no_rc{
      public:
  
        inline void inc_ref() { }
        inline bool dec_ref() { return false; }
      };
  
  #else
  
      template<typename T>
      class rc{
      public:
        rc() : ref_count(0) {}
  
        inline void inc_ref() { ref_count++; }
        inline bool dec_ref() { return (--ref_count == 0); }
  
      private:
        T ref_count;
      };    
  
      #if defined(ERMINE_DISABLE_MULTI_THREADING) || !defined(ERMINE_STD_LIB)
        #define ERMINE_RC_POLICY memory::gc::rc<ERMINE_RC_TYPE>
      #endif
  
      #if defined(ERMINE_STD_LIB) && !defined(ERMINE_DISABLE_MULTI_THREADING)
        #define ERMINE_RC_POLICY memory::gc::rc<::std::atomic<ERMINE_RC_TYPE>>
      #endif
  #endif
    }
  }
  #endif
  template<typename>
  void type_id(){}
  
  using type_id_t = void(*)();
  typedef type_id_t type_t;
  
  class var;
  typedef var const & ref;
  class seekable_i;
  
  template <typename rc>
  class object_i : public rc{
  public:
    object_i() { }
    virtual ~object_i() { };
  
    virtual type_t type() const = 0;
  
  #if !defined(ERMINE_DISABLE_STD_OUT)
    virtual void stream_console() const {
      rt::print(\"var#\");
      const void* addr = this;
      rt::print(addr);
    }
  #endif
  
    virtual bool equals(ref) const;
  
    virtual seekable_i* cast_seekable_i() { return nullptr; }
  
    void* operator new(size_t, void* ptr){ return ptr; }
    void  operator delete(void * ptr){ ERMINE_ALLOCATOR::free(ptr); }
  };
  
  typedef object_i<ERMINE_RC_POLICY> object;
  #if !defined(ERMINE_POINTER_T)
    #define ERMINE_POINTER_T memory::pointer<object>
  #endif
  
  typedef ERMINE_POINTER_T pointer_t;
  class var{
  public:
    explicit inline var(object* o = nullptr) : obj(o) { inc_ref(); }
    inline var(ref o)   : obj(o.obj) { inc_ref(); }
    inline var(var&& o) : obj(o.detach()) { }
  
    ~var() { dec_ref(); }
  
    inline var& operator=(var&& other){
      if (this != &other){
        dec_ref();
        obj = other.detach();
      }
      return *this;
    }
  
    inline var& operator= (ref other){
      if (obj != other.obj){
        dec_ref();
        obj = other.obj;
        inc_ref();
      }
      return *this;
    }
  
    bool equals (ref) const;
  
    bool operator==(ref other) const { return equals(other); }
  
    bool operator!=(ref other) const { return !equals(other); }
  
    void* operator new(size_t, void* ptr){ return ptr; }
  
    operator bool() const;
  
  #if !defined(ERMINE_DISABLE_STD_OUT)
    void stream_console() const {
      if (obj != nullptr )
        obj->stream_console();
      else
        rt::print(\"nil\");
    }
  #endif
  
    inline object* get() const { return obj; }
  
    template<typename T>
    inline T* cast() const { return static_cast<T*>((object*)obj); }
  
    inline bool is_type(type_t type) const {
      if (obj)
        return (static_cast<object*>(obj)->type() == type);
      return false;
    }
  
    inline bool is_nil() const { return (obj == nullptr); }
  
  private:
    object* detach(){
      object* _obj = obj;
      obj = nullptr;
      return _obj;
    }
  
    inline void inc_ref(){
  #if !defined(ERMINE_DISABLE_RC)
      // Only change if non-null
      if (obj) obj->inc_ref();
  #endif
    }
  
    inline void dec_ref(){
  #if !defined(ERMINE_DISABLE_RC)
      // Only change if non-null
      if (obj){
        // Subtract and test if this was the last pointer.
        if (obj->dec_ref()){
          delete obj;
          obj = nullptr;
        }
      }
  #endif
    }
  
    pointer_t obj;
  };
  
  template<>
  inline seekable_i* var::cast<seekable_i>() const { return obj->cast_seekable_i(); }
  
  template <typename rc>
  bool object_i<rc>::equals(ref o) const {
    return (this == o.get());
  }
  
  #ifdef ERMINE_STD_LIB
  std::ostream &operator<<(std::ostream &os, var const &v) {
    v.stream_console();
    return os;
  }
  #endif
  template<typename FT, typename... Args>
  inline var obj(Args... args) {
    void * storage = ERMINE_ALLOCATOR::allocate<FT>();
    return var(new(storage) FT(args...));
  }
  
  inline var nil(){
    return var();
  }
  #undef alloca
  
  template<typename T>
  class alloca {
  
    byte memory [sizeof(T)];
    
  public:
    
    template<typename... Args>
    inline explicit alloca(Args... args) {
      (new(memory) T(args...))->inc_ref();
    }
  
    inline operator object*() {
      return (object*)memory;
    }
  };
  
}

namespace ermine{
  template <typename T>
  class array {
    size_t  _size{0};
  
  public:
  
    T* data {nullptr};
  
    explicit inline array(size_t s = 0) : _size(s) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
    }
  
    explicit inline array(const T* source, size_t s = 0) : _size(s) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
      for(size_t i = 0; i < _size; i++)
        data[i] = source[i];
    }
  
  #if defined(ERMINE_STD_LIB)
    explicit inline array(std::initializer_list<T> source) :
      _size(source.size()) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
      size_t idx = 0;
      for(auto item : source){  
        data[idx] = item;
        idx++;
      }
    }
  #endif
  
    inline array(array&& m) :
      data(m.data), _size(m.size()) { m.data = nullptr; }
  
    inline array(array& m) : _size(m.size()){
      for(size_t i = 0; i < _size; i++)
        data[i] = m.data[i];
    }
    
    ~array(){
      ERMINE_ALLOCATOR::free(data);
    }
  
  
    inline array& operator=(array&& x){
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }
  
    inline T& operator [](size_t idx)      { return data[idx]; }
    inline T operator [](size_t idx) const { return data[idx]; }
  
    inline T*      begin() const { return &data[0];      }
    inline T*      end()   const { return &data[_size];  }
    inline size_t  size()  const { return _size;         }
  };
}

// Runtime Prototypes
namespace ermine{
    namespace runtime {
      var list(ref v);
      template <typename... Args>
      var list(ref first, Args const & ... args);
  
      inline bool is_seqable(ref seq);
  
      inline var first(ref seq);
      inline var rest(ref seq);
      inline var cons(ref x, ref seq);
  
      var nth(var seq, number_t index);
      var nthrest(var seq, number_t index);
  
      inline size_t count(ref seq);
  
      inline var range(number_t low, number_t high);
    }
  
  #define for_each(x,xs) for(var _tail_ = rt::rest(xs), x = rt::first(xs); !_tail_.is_nil(); x = rt::first(_tail_), _tail_ = rt::rest(_tail_))
  template<typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args);
  
  template<typename T>
  inline var run(T const & fn);
  
  template<>
  inline var run(ref);
  
  namespace runtime{
    inline var apply(ref fn, ref argv);
  }
}
"
     :native_headers       native-headers
     :objects              objects
     :symbols              symbol-table
     :native_declarations  native-declarations
     :ermine_cpp           "
namespace ermine{
  namespace runtime {
    inline bool is_seqable(ref coll){
      if(coll.cast<seekable_i>())
        return true;
      else
        return false;
    }
  
    inline var first(ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->first();
    }
  
    inline var rest(ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->rest();
    }
  
    inline var cons(ref x, ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return rt::list(x);
      return seq.cast<seekable_i>()->cons(x);
    }
  
    var nth(var seq, number_t index){
      if (index < 0)
        return nil();
  
      for(number_t i = 0; i < index; i++)
        seq = rt::rest(seq);
      return rt::first(seq);
    }
  
    var nthrest(var seq, number_t index){
      for(number_t i = 0; i < index; i++)
        seq = rt::rest(seq);
  
      if (seq.is_nil())
        return rt::list(); 
  
      return seq;
    }
  
    inline size_t count(ref seq){
      size_t acc = 0;
  
      for(var tail = rt::rest(seq);
          !tail.is_nil();
          tail = rt::rest(tail))
        acc++;
  
      return acc;
    }
  
    inline var range(number_t low, number_t high){
      class seq : public lambda_i {
        number_t low, high;
      public:
        explicit seq(number_t l, number_t h) : low(l), high(h) { }
        var invoke(ref) const final {
          if (low < high)
            return obj<lazy_sequence>(obj<number>(low), obj<seq>((low + 1), high));
          return nil();
        }
      };
      return obj<lazy_sequence>(obj<seq>(low, high));
    }
  }
  template<typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args) {
    return fn.invoke(rt::list(args...));
  }
  
  template<typename T>
  inline var run(T const & fn) {
    return fn.invoke(nil());
  }
  
  template<>
  inline var run(ref fn) {
    return fn.cast<lambda_i>()->invoke(nil());
  }
  
  template<typename... Args>
  inline var run(ref fn, Args const & ... args) {
    return fn.cast<lambda_i>()->invoke(rt::list(args...));
  }
  
  namespace runtime {
    inline var apply(ref f, ref argv){
      if (rt::rest(argv).is_type(type_id<empty_sequence>))
        return f.cast<lambda_i>()->invoke(rt::first(argv));
  
      struct{
        var operator()(ref seq) const {
          ref head = rt::first(seq);
  
          if (head.is_nil())
            return cached::empty_sequence_o;
  
          if (head.cast<seekable_i>())
            return head;
  
          return rt::cons(head, (*this)(rt::rest(seq)));
        }
      } spread;
  
      return f.cast<lambda_i>()->invoke(spread(argv));
    }
  }
}
"
     :lambda_classes       (lambda-definitions lambdas)
     :lambda_bodies        (lambda-implementations lambdas)
     :body                 (filter #(not (empty? %)) body)
     :ermine_main          main)))

(defn compile-options [& [options]]
  (merge {:compiler "g++"
          :compiler-options ["-std=c++11"]
          :source-extension extension-cpp
          :base-name "solution"}
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
          output-path      (file-path output)
          output-extension (if (args :output) 
                             (file-extension (args :output))
                             extension-cpp)
          base-name        (file-base-name output)
          input-path       (file-path input)
          output-file      (make-file output-path base-name output-extension)
          default-options  (compile-options-parse-source output-file)]
      (-> default-options
          (assoc :input-file         input)
          (assoc :base-name          base-name)
          (assoc :path               input-path)
          (assoc :output-path        output-path)
          (assoc :source-extension   output-extension)
          (assoc :ast                (args :ast))
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
    (write-to-file file-name program)
    true))

(defn build-solution [spec-fn]
  (let [{:keys [input-file path]} (spec-fn)]

    (compile->cpp (read-clojure-file input-file) (spec-fn))))

(def program-options
  [["-i" "--input FILE"         "Input File" :default "./core.clj"]
   ["-o" "--output FILE"        "Output C++ File"]
   [nil  "--global-functions"   "Disables inline-global-fns Optimization"]
   [nil  "--ast"                "Print Intermediate AST"]])

(defn -main [& args]
  (try
    (let [args (parse-opts args program-options)
          {:keys [input]} (:options args)]

      (when (not (file-exists input))
        #_(warn "no input file")
        (exit-failure))

      (let [specs (build-specs input args)]

        (build-solution specs))
      (exit-success))
    (catch Exception e
      (stacktrace/print-stack-trace e 10))))
