(ns ermine.core
  (:refer-clojure :exclude [compile])
  (:import (org.apache.commons.io FileUtils)
           (org.apache.commons.lang StringEscapeUtils)
           (org.antlr.stringtemplate StringTemplate))
  (:require [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [fast-zip.core :as zip]
            [flatland.ordered.map :as ordered-map]))

(defn stringify [any]
  (if (keyword? any) (name any) (str any)))

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
  (let [m (into (hash-map) mp)
        k (keys m)
        v (vals m)]
    (zipmap
     (map stringify k)
     (scan-kv-to-sv v))))

(defmacro render-template [template & vars]
  `(let [vars# (hash-map ~@vars)
         view# (StringTemplate. ~template)]
     (doseq [[k# v#] vars#]
       (.setAttribute view# (stringify (name k#)) (each-kv-to-sv v#)))
     (.toString view#)))

(defn read-file [f] (FileUtils/readFileToString (io/file f)))
(defn write-file [f s] (FileUtils/writeStringToFile (io/file f) (.trim s)))

(defn escape-string [s] (StringEscapeUtils/escapeJava s))

(defn form?
  ([s] (fn [f] (form? s f)))
  ([s f] (and (seq? f) (= (first f) s))))

(defn symbol-set [form] (into (hash-set) (filter symbol? (flatten form))))

(defn split-fn [sig]
  (let [name (if (symbol? (second sig)) (second sig) nil)
        sig  (if name (drop 2 sig) (rest sig))
        [args & body] sig]
    [name args body]))

(defn ffi-fn? [body]
  (and (not (nil? body))
       (not (empty? body))
       (every? true? (map string? body))))

(defn fn-arg-symbol? [s]
  (and (symbol? s)
       (not (= s '&))
       (not (= s '_))
       (not (= s 'fir-destructure-associative))))

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
  (if (every? true? (map pred tree))
    (list)
    (loop [loc (zip/seq-zip tree)]
      (if (zip/end? loc)
        (zip/root loc)
        (recur
         (zip/next
          (if (pred (zip/node loc))
            (zip/remove loc)
            loc)))))))

(defn parser-peek [tree pred & [node-fn]]
  (let [node-fn (or node-fn zip/node)]
    (loop [loc (zip/seq-zip tree)
           nodes (vector)]
      (if (zip/end? loc)
        nodes
        (recur
         (zip/next loc)
         (if (pred (zip/node loc))
           (conj nodes (node-fn loc))
           nodes))))))

(defn new-symbol [& parts] (symbol (apply str (map (fn [%] (.replace (str %) "." "_")) parts))))

(defn fn-make-unique [args body]
  (if (string? (first body))
    [args body]
    (let [syms     (filter fn-arg-symbol? (flatten args))
          replace? (apply hash-map (interleave syms (map (fn [%] (new-symbol % (gensym "__"))) syms)))
          body     (transform body replace? replace?)
          replace? (merge replace? (hash-map 'fir-new-map 'fir-destructure-associative))
          args     (transform args replace? replace?)]
      [args body])))

(defn new-fir-fn [& {:keys [name args body escape] :or {escape true, args (vector)}}]
   (let [name-unique (when name
                       (new-symbol name (gensym "__")))
         [args body] (if escape
                       (fn-make-unique args body)
                       [args body])
         body        (if name-unique
                       (transform body (fn [%] (= % name)) (fn [_] name-unique))
                       body)]
     (if name-unique
       `(fn* ~name-unique ~args ~@body)
       `(fn* ~args ~@body))))

(defn append-to! [r ks v]
  (let [cv (reduce (fn [h v] (v h)) (deref r) ks)]
    (swap! r assoc-in ks (conj cv v))
    ""))

(defn read-ermine [f]
  (let [ns (gensym)
        ns-str (str ns)]
    (create-ns ns)
    (binding [*ns* (the-ns ns)]
      (refer 'clojure.core)
      (let [form (read-string (str "(" (read-file f) ")"))
            form (transform form symbol? (fn [%] (if (= (namespace %) ns-str) (symbol (name %)) %)))]
        (transform form
         (fn [x]
           (and (form? 'quote x)
                (or (= 'clojure.core/fn   (second x))
                    (= 'clojure.core/defn (second x)))))
         (fn [[_ s]] `'~(symbol (name s))))))))

(defn macro-normalize [f] (transform f (form? 'let) (fn [[_ bindings & body]] `(~'let* ~(apply list bindings) ~@body))))

(defn expand-macros-single [form]
  (let [core-macros (filter (form? 'defmacro) (read-ermine "ermine/lang.clj"))
        core-macro-symbols (into (hash-set) (map second core-macros))
        form-macros (remove (fn [[_ name]] (core-macro-symbols name)) (filter (form? 'defmacro) form))
        form-macro-symbols (map second form-macros)
        form (parser-drop form (form? 'defmacro))
        ns# (gensym)
        macro-symbols (concat core-macro-symbols form-macro-symbols)]

    (create-ns ns#)
    (binding [*ns* (the-ns ns#)]
      (refer 'clojure.core :exclude (concat macro-symbols ['fn 'def]))
      (use '[ermine.core :only [new-fir-fn symbol-conversion]])

      (doseq [m (concat core-macros form-macros)]
        (eval m)))

    (let [form (transform (macro-normalize form)
                (fn [f]
                  (some true? (map (fn [%] (form? % f)) macro-symbols)))
                (fn [f]
                  (binding [*ns* (the-ns ns#)]
                    (transform (walk/macroexpand-all f) symbol? (fn [%] (symbol (name %)))))))]
      (remove-ns ns#)
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
   (let [shakeable? (form? 'defn)
         header-symbols (symbol-set (parser-peek header seq?))
         header-fns (into (hash-map) (map (fn [%] (vector (second %) %)) (parser-peek header shakeable?)))
         header-non-shakeable (parser-drop header shakeable?)
         form-expanded (expand-macros (concat header-non-shakeable form))
         fns (atom (hash-set))
         _ (shake-concat form-expanded header-fns fns header-non-shakeable)
         header-shaked (parser-drop header (fn [f] (and (shakeable? f) (not ((deref fns) (second f))))))]
     (concat header-shaked form)))
  ([form built-in fns non-shakeable]
   (transform form symbol?
        (fn [s]
          (let [f (built-in s)]
            (when (and f (not ((deref fns) s)))
              (swap! fns conj s)
              (shake-concat (expand-macros (concat non-shakeable f)) built-in fns non-shakeable)) s)))))

(defn escape-fn-calls [form]
  (let [arity (parser-peek form (fn [f] (and (form? 'fir-defn-heap f) (not (empty? (parser-peek f (form? 'fir-defn-arity)))))))
        arity (reduce
               (fn [h [_ name _ _ [_ dispatch [_ default]] :as form]]
                 (let [jmp (if default (hash-map :default default) (hash-map))
                       jmp (reduce (fn [h [arity [_ call]]] (assoc h arity call)) jmp dispatch)]
                   (assoc h name jmp)))
               (hash-map) arity)
        arity-renames (reduce (fn [h [name jmps]]
                                (reduce (fn [h jump] (assoc h jump (gensym (str name "__")))) h (vals jmps)))
                              (hash-map) arity)
        ;; resolve arity calls
        form (transform form
                (form? 'fir-defn-arity)
                (fn [f]
                  (transform f (form? 'fir-fn-heap) (fn [[_ & f]] `(~'fir-fn-stack ~@f)))))
        form (transform form
                (fn [f]
                  (and (seq? f)
                       (form? 'fir-fn-heap (first f))
                       (arity (second (first f)))))
                (fn [f]
                  (let [[[_ fn] & args] f
                        dispatch ((arity fn) (count args))
                        default  ((arity fn) :default)]
                    (cond dispatch `((~'fir-fn-heap ~dispatch) ~@args)
                          default  `((~'fir-fn-heap ~default)  ~@args)
                          :else f))))
        form (transform form
                (fn [f] (and (symbol? f) (arity-renames f)))
                (fn [f] (arity-renames f)))
        ;; resolve fn calls
        form (transform form
                (fn [f] (and (seq? f) (form? 'fir-fn-heap (first f))))
                (fn [f] (let [[[_ & fn] & args] f] `((~'fir-fn-stack ~@fn) ~@args))))]
    form))

(defn escape-fn-inheritance [form]
  (let [heap-fns (into (hash-set) (map second (parser-peek form (form? 'fir-fn-heap))))
        stack-fns (into (hash-set) (map second (parser-peek form (form? 'fir-fn-stack))))
        escapeable-fns (set/difference stack-fns heap-fns)]
    (transform form
        (fn [f] (and (seq? f) (= (first f) 'fir-defn-heap) (escapeable-fns (second f))))
        (fn [[_ & f]] `(~'fir-defn-stack ~@f)))))

(defn let-closure [bindings body]
  (if (empty? bindings)
    `((~'fir-let-fn (list) ~@body))
    (apply
     (fn close [[arg val] & more]
       (if (empty? more)
         `((~'fir-let-fn [~arg] ~@body) ~val)
         `((~'fir-let-fn [~arg] ~(apply close more)) ~val)))
     (partition 2 bindings))))

(defn let-assert [bindings body]
  (when (odd? (count bindings))
    (throw (Error. (str "let requires an even number of forms in binding vector => " bindings)))))

(defn let->fn [form]
  (let [form (transform form (form? 'let*) (fn [[_ bindings & body]] (let-assert bindings body) (let-closure bindings body)))
        form (transform form (form? 'fir-let-fn) (fn [[_ args & body]] (new-fir-fn :args args :body body)))]
    form))

(defn do->fn [form]
  (transform form (form? 'do) (fn [f] `(~(new-fir-fn :body (rest f))))))

(defn fn-defined? [fns env args body]
  (let [fn-name ((deref fns) (concat [env args] body))]
    (when fn-name
      (apply list 'fir-fn-heap fn-name env))))

(defn define-fn [fns env name args body]
  (let [name (or name (gensym "FN__"))]
    (swap! fns assoc (concat [env args] body) name)
    (apply list 'fir-fn-heap name env)))

(defn fn->lift
  ([form]
   (let [fns  (atom (ordered-map/ordered-map))
         form (fn->lift form fns)
         fns  (map (fn [[body name]] (concat ['fir-defn-heap name] body)) (deref fns))]
     (concat fns form)))
  ([form fns & [env]]
   (transform
    form
    (form? 'fn*)
    (fn [sig]
      (let [[name args body] (split-fn sig)
            ;; transform named recursion in body
            body (if name
                   (transform body (form? name) (fn [[_ & args]] (cons (apply list 'fir-fn-heap name env) args)))
                   body)
            body (fn->lift body fns (concat args env))
            symbols (symbol-set body)
            env  (into (list) (set/intersection symbols (into (hash-set) (flatten env))))
            args (if (ffi-fn? body)
                   args
                   (transform args symbol? (fn [v] (if (or (not (fn-arg-symbol? v)) (symbols v)) v '_))))]
        (or (fn-defined? fns env args body) (define-fn fns env name args body)))))))

(defn escape-cpp-symbol [s]
  (clojure.string/escape (str s) (hash-map \- "_", \* "_star_", \+ "_plus_", \/ "_slash_", \< "_lt_", \> "_gt_", \= "_eq_", \? "_QMARK_", \! "_BANG_", \# "_")))

(defn symbol-conversion [form]
  (transform form symbol? (comp (fn [%] (symbol (escape-cpp-symbol %))) (fn [%] (if (= 'not %) '_not_ %)))))

(defn inline-defn? [f]
  (and (form? 'def f)
       (not (= (:tag (meta (second f))) 'volatile))
       (form? 'fir-fn-heap (first (drop 2 f)))))

(defn fn->inline [form]
  (if (:global-functions nil)
    form
    (let [defns      (filter (fn [%] (= (count (last %)) 2)) (parser-peek form inline-defn?))
          fn-table   (map (fn [[_ name [_ gensym]]] [name gensym]) defns)
          impl-table (apply hash-map (flatten fn-table))
          defn?      (fn [f] (and (inline-defn? f) (impl-table (second f))))
          invoke     (fn [f] (let [imp (impl-table f)] (if imp (list 'fir-fn-heap imp) f)))
          no-defn    (reduce (fn [h v] (parser-drop h defn?)) form defns)
          inlined    (reduce (fn [h [name gensym]]
                               (transform h (fn [%] (or (form? name %) (form? 'def %))) (fn [f] (map invoke f))))
                             no-defn fn-table)]
      (reduce (fn [h [name gensym]]
                (transform h (fn [%] (and (symbol? %) (= % gensym))) (fn [_] (identity name))))
              inlined fn-table))))

(defn escape-analysis [form] (escape-fn-inheritance (escape-fn-calls form)))

(defn compile [form]
  (symbol-conversion (escape-analysis (fn->inline (fn->lift (do->fn (let->fn (expand-macros (shake-concat (read-ermine "ermine/lang.clj") form)))))))))

(defmulti emit (fn [f _]
                 (cond (form? '(fir_fn_stack list) f)  'fir_inline_list
                       (form? '(fir_fn_stack first) f) 'fir_inline_first
                       (form? '(fir_fn_stack rest) f)  'fir_inline_rest
                       (form? 'fir_defn_heap f)        'fir_defn_heap
                       (form? 'fir_defn_stack f)       'fir_defn_stack
                       (form? 'fir_defn_arity f)       'fir_defn_arity
                       (form? 'fir_fn_heap f)          'fir_fn_heap
                       (form? 'fir_fn_stack f)         'fir_fn_stack
                       (form? 'list f)                 'list
                       (form? 'defobject f)            'defobject
                       (form? 'native_header f)        'native_header
                       (form? 'native_declare f)       'native_declare
                       (form? 'native_define f)        'native_define
                       (form? 'if f)                   'if
                       (form? 'def f)                  'def
                       (form? 'fir_new_map f)          'fir_new_map
                       (symbol? f)               :symbol
                       (keyword? f)              :keyword
                       (number? f)               :number
                       (nil? f)                  :nil
                       (char? f)                 :char
                       (string? f)               :string
                       (or (true? f) (false? f)) :boolean
                       (seq? f)                  :invoke-fn
                       :else                     :unsupported-form)))

(defmethod emit :unsupported-form [form _] (throw (Error. (str "unsupported form => " form))))

(defn emit-ast [ast state]
  (reduce (fn [h v] (conj h (emit v state))) (vector) ast))

(defn emit-source [form]
  (let [state (atom (hash-map
                     :native-headers (vector)
                     :native-declarations (vector)
                     :objects (vector)
                     :symbol-table (hash-set)
                     :lambdas (vector)
                     :native-defines (vector)))
        ast (compile form)
        body (emit-ast ast state)]
    (assoc (deref state) :body body)))

(defmethod emit :symbol [form _] (str form))

(defmethod emit :string [form _] (str "obj<string>(\"" (escape-string form) "\"," (count form) ")"))

(defmethod emit :boolean [form _] (if (true? form) "cached::true_o" "cached::false_o"))

(defmethod emit :nil [form _] "nil()")

(defmethod emit :keyword [form _] (str "obj<keyword>(" (reduce (fn [h v] (+ h (int v))) 0 (str form)) ")"))

(defmethod emit :char [form _] (str "obj<number>(" (int form) ")"))

(defmethod emit :number [form _] (str "obj<number>(" (double form) ")"))

(defmethod emit 'fir_new_map [[_ & kvs] state]
  (let [kvs (partition 2 kvs)
        keys (interpose ", " (map (fn [%] (emit (first %) state)) kvs))
        vals (interpose ", " (map (fn [%] (emit (second %) state)) kvs))]
    (str "obj<map_t>(rt::list(" (apply str keys) "), rt::list(" (apply str vals) "))")))

(defmethod emit 'def [[_ name & form] state]
  (append-to! state [:symbol-table] name)
  (str "(" name " = " (apply str (emit-ast form state)) ")"))

(defmethod emit 'if [[_ test then else] state]
  (let [test (emit test state)
        then (emit then state)
        else (if (nil? else) "nil()" (emit else state))]
    (apply str "(" test " ? " then " : " else ")")))

(defmethod emit 'list [[fn & args] state]
  (let [elements (apply str (interpose ", " (emit-ast args state)))]
    (str "rt::list(" elements ")")))

(defmethod emit 'defobject [[_ spec] state] (append-to! state [:objects] spec))

(defmethod emit 'native_header [[_ & declarations] state] (append-to! state [:native-headers] declarations))

(defmethod emit 'native_declare [[_ declaration] state] (append-to! state [:native-declarations] declaration))

(defmethod emit 'native_define [[_ define] state] (append-to! state [:native-defines] define))

(defmethod emit 'fir_inline_list [[_ & args] state] (str "rt::list(" (apply str (interpose ", " (emit-ast args state))) ")"))

(defmethod emit 'fir_inline_first [[_ & seq] state] (str "rt::first(" (apply str (emit-ast seq state)) ")"))

(defmethod emit 'fir_inline_rest [[_ & seq] state] (str "rt::rest(" (apply str (emit-ast seq state)) ")"))

(defn norm-fn-env [env] (remove (fn [%] (or (= % '&) (= % '_) (= % :as))) (flatten env)))

(defn new-fn-heap [l]
  (let [n (second l)
        e (norm-fn-env (drop 2 l))]
    (if (empty? e)
      (str "obj<" n ">()")
      (str "obj<" n ">(" (apply str (interpose ", " e)) ")"))))

(defn new-fn-stack [l]
  (let [n (second l)
        e (norm-fn-env (drop 2 l))]
    (if (empty? e)
      (str n "()")
      (str n "(" (apply str (interpose ", " e)) ")"))))

(defn invoke-fn [n args]
  (if (empty? args)
    (str "run(" n ")")
    (str "run(" n ", " (apply str (interpose ", " args)) ")")))

(declare destructure-arguments)

(defn destructure-nth-rest [parent pos]
  (reduce (fn [h v] (str v "(" h ")")) parent (repeat pos "rt::rest")))

(defn destructure-nth [parent pos]
  (str "rt::first(" (destructure-nth-rest parent pos) ")"))

(defn destructure-get [name parent key]
  (str "ref " name " = " parent ".cast<map_t>()->val_at(rt::list(" (emit key nil) "));"))

(defn new-fn-arg [name parent pos]
  (let [value (destructure-nth parent pos)]
    (condp = (:tag (meta name))
      'bool_t   (str "bool " name " = " "bool(" value ")")
      'real_t   (str "real_t " name " = " "number::to<real_t>(" value ")")
      'number_t (str "number_t " name " = " "number::to<number_t>(" value ")")
      'size_t   (str "size_t " name " = " "number::to<size_t>(" value ")")
      'byte     (str "byte " name " = " "number::to<byte>(" value ")")
      'c_str    (str "var " name "_packed = string::pack(" value ");\n"
                     "char* " name " = " "string::c_str(" name "_packed)")
      (str "ref " name " = " value))))

(defn new-fn-var-arg [name parent pos]
  (str "ref " name " = " (destructure-nth-rest parent pos)))

(defn destructure-associative [name parent pos]
  (let [tmp# (gensym)]
    [(new-fn-arg tmp# parent pos) (map (fn [[s k]] (destructure-get s tmp# k)) name)]))

(defn destructure-sequential [args parent]
  (reduce
   (fn [h [pos name]]
     (let [name (cond
                  (symbol? name)
                    (new-fn-arg name parent pos)
                  (form? 'fir_destructure_associative name)
                    (let [[_ & args] name, args (apply hash-map (flatten (remove (fn [%] (= (first %) '_)) (partition 2 args))))]
                      (destructure-associative args parent pos))
                  (coll? name)
                    (destructure-arguments name (destructure-nth parent pos)))]
       (conj h name))) (vector) args))

(defn destructure-var-args [name parent pos]
  (cond (nil?    name) (vector)
        (symbol? name) (new-fn-var-arg name parent pos)
        (coll?   name) (let [tmp# (gensym)]
                         [(new-fn-var-arg tmp# parent pos) (destructure-arguments name tmp#)])))

(defn destructure-as-arg [name parent]
  (if (symbol? name) (new-fn-var-arg name parent 0) (vector)))

(defn destructure-arguments
  ([args] (flatten (destructure-arguments args "_args_")))
  ([args parent]
   (let [t-args       args
         args         (take-while (fn [%] (and (not (= % '&)) (not (= % :as)))) t-args)
         var-args     (second (drop-while (fn [%] (not (= % '&))) t-args))
         as-arg       (second (drop-while (fn [%] (not (= % :as))) t-args))
         args-indexed (remove (fn [%] (= (second %) '_)) (map-indexed (fn [p v] [p v]) args))
         as-arg       (destructure-as-arg as-arg parent)
         var-args     (destructure-var-args var-args parent (count args))
         args         (destructure-sequential args-indexed parent)]
     [args var-args as-arg])))

(defmethod emit :invoke-fn [[fn & args] state] (invoke-fn (emit fn state) (emit-ast args state)))

(defmethod emit 'fir_fn_heap [f _] (new-fn-heap f))

(defmethod emit 'fir_fn_stack [f _] (new-fn-stack f))

(defn emit-lambda [name env args body state]
  (let [native-declarations (filter (form? 'native_declare) body)
        return (fn [b] (conj (pop b) (str "return " (last b))))
        body (remove (form? 'native_declare) body)
        body (cond (empty? body)
                    ["return nil()"]
                    ;; multi arity dispacth
                    (form? 'fir_defn_arity (first body))
                    (return
                     (emit (first body) state))
                    ;; ffi call
                    (ffi-fn? body)
                    (let [buffer (StringBuilder.)]
                      (doseq [b body]
                        (.append buffer b))
                      (let [body (.toString buffer)]
                        (cond
                          (.contains body "__result") ["var __result" body "return __result"]
                          (.contains body "return") [body]
                          :else [body "return nil()"])))
                    ;; s-expression
                    :else (return
                              (emit-ast body state)))
        env  (norm-fn-env env)
        vars (destructure-arguments args)]
    (doseq [dec native-declarations]
      (emit dec state))
    (hash-map :name name :env env :args args :vars vars :body body)))

(defmethod emit 'fir_defn_heap [[_ name env args & body] state] (append-to! state [:lambdas] (emit-lambda name env args body state)))

(defmethod emit 'fir_defn_stack [[_ name env args & body] state] (append-to! state [:lambdas] (assoc (emit-lambda name env args body state) :stack true)))

(defmethod emit 'fir_defn_arity [[_ switch default] _]
  (let [default (if default
                  (str (new-fn-stack default) ".invoke(_args_)")
                  "nil()")
        switch  (render-template
                 "switch (rt::count(_args_)) {
                  $fns: {fn|
                    case $fn.case$:
                       return $fn.fn$.invoke(_args_); };separator=\"\n\"$
                  }"
                 :fns (map (fn [[s f]] (hash-map :fn (new-fn-stack f) :case s)) switch))]
    [switch default]))

(defn lambda-definitions [fns]
  (render-template
   "$fns: {fn|
      $if(!fn.stack)$
       struct $fn.name$ final : lambda_i {
      $else$
       struct $fn.name$ \\{
      $endif$
        $fn.env:{const var $it$;} ;separator=\"\n\"$

        $if(fn.env)$
          explicit $fn.name$ ($fn.env:{ref $it$} ;separator=\",\"$) : $fn.env:{$it$($it$)} ;separator=\",\"$ { }
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

(defn program-template [source]
  (let [{:keys [body lambdas symbol-table native-headers objects native-declarations native-defines]} source
        native-headers (into (hash-set) (flatten native-headers))
        file-ns        (escape-cpp-symbol "_main")
        main           (render-template
                        "
#if !defined(ERMINE_DISABLE_STD_MAIN)
  int main()
  {
    using namespace ermine;
    ERMINE_ALLOCATOR::init();

    $file$::main();

   #if defined(ERMINE_PROGRAM_MAIN)
    run(ERMINE_PROGRAM_MAIN);
   #endif

    return 0;
  }
#endif
"
                        :file file-ns)]
    (render-template
     "
        $native_defines:{$it$} ;separator=\"\n\"$
        $native_headers:{#include \"$it$\"} ;separator=\"\n\"$

        #ifndef ERMINE_RUNTIME_H
        #define ERMINE_RUNTIME_H
         $ermine_h$
        #endif

        // Objects
        namespace ermine {
         $objects:{$it$} ;separator=\"\n\"$
        }

        // Symbols
        namespace $file$ {
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
        namespace $file$ {
          $lambda_classes:{$it$} ;separator=\"\n\"$
        }

        // Lambda Implementations
        namespace $file$ {
          $lambda_bodies:{$it$} ;separator=\"\n\"$
        }

        // Program Run
        namespace $file$ {
         void main() {
          $body:{$it$;} ;separator=\"\n\"$
         }
        }

        $ermine_main$"
     :file           file-ns
     :native_defines native-defines
     :ermine_h       "
// Detect Hardware
#define ERMINE_CONFIG_SAFE_MODE TRUE

#if defined(__APPLE__) || defined(_WIN32) || defined(__linux__) || defined(__unix__) || defined(_POSIX_VERSION)
  #undef ERMINE_CONFIG_SAFE_MODE
  #define ERMINE_STD_LIB TRUE
#endif

#if defined(ERMINE_CONFIG_SAFE_MODE)
  #define ERMINE_DISABLE_MULTI_THREADING TRUE
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

namespace ermine {
  namespace runtime { }
  namespace rt = runtime;

  // Types
  typedef uint8_t byte;

  // Concurrency
  #if defined(ERMINE_DISABLE_MULTI_THREADING)
    struct mutex {
      void lock()   { }
      void unlock() { }
    };
  #else
    #if defined(ERMINE_STD_LIB)
      struct mutex {
        ::std::mutex m;

        void lock()   { m.lock();   }
        void unlock() { m.unlock(); }
      };
    #endif
  #endif

  struct lock_guard {
    mutex & _ref;

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

  template <size_t S, typename word_t = ERMINE_BITSET_WORD_TYPE>
  struct bitset {
    static const size_t bits_per_word = sizeof(word_t) * 8;
    static const size_t n_words = S / bits_per_word;

    static_assert((S % bits_per_word) == 0, \"bitset size must be a multiple of word_t\");

    word_t bits[n_words];

    inline size_t word (size_t i) const { return i / bits_per_word; }
    inline size_t bit  (size_t i) const { return i % bits_per_word; }

    bitset() : bits{ word_t(0x00) } { }

    inline void set (size_t b) {
      bits[word(b)] = (word_t)(bits[word(b)] | (word_t(1) << (bit(b))));
    }

    inline void set (size_t b, size_t e) {
      size_t word_ptr = word(b);
      size_t n_bits = e - b;

      bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(bit(b), n_bits));

      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for ( ; word_ptr < last_word; word_ptr++) {
        bits[word_ptr] = (word_t)(bits[word_ptr] | bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }

    inline void reset (size_t b) {
      bits[word(b)] = (word_t)(bits[word(b)] & ~(word_t(1) << (bit(b))));
    }

    inline void reset (size_t b, size_t e) {
      size_t word_ptr = word(b);
      size_t n_bits = e - b;

      bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(bit(b), n_bits));

      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for ( ; word_ptr < last_word; word_ptr++) {
        bits[word_ptr] = (word_t)(bits[word_ptr] & ~bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }

    inline void flip (size_t b) {
      bits[word(b)] = (word_t)(bits[word(b)] ^ (word_t(1) << (bit(b))));
    }

    inline void flip (size_t b, size_t e) {
      size_t word_ptr = word(b);
      size_t n_bits = e - b;

      bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(bit(b), n_bits));

      n_bits -= bits_per_word - bit(b);
      word_ptr++;
      size_t last_word = (word(e) == n_words) ? n_words : word(e) + 1;
      for ( ; word_ptr < last_word; word_ptr++) {
        bits[word_ptr] = (word_t)(bits[word_ptr] ^ bit_block(0, n_bits));
        n_bits -= bits_per_word;
      }
    }

    inline bool test (size_t b) const {
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
        for ( ; word_ptr < last_word; word_ptr++) {
          this_word = bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for (size_t i = b; i < e; i++)
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
        for ( ; word_ptr < last_word; word_ptr++) {
          this_word = ~bits[word_ptr];
          if (this_word != static_cast<word_t>(0))
            return ((word_ptr * bits_per_word) + (size_t) __builtin_ctz(this_word));
        }
  #else
        for (size_t i = b; i < e; i++)
          if (!test(i))
            return i;
  #endif
      return S;
    }

    // Return word with length-n bit block starting at bit p set.
    // Both p and n are effectively taken modulo bits_per_word.
    static inline word_t bit_block(size_t p, size_t n) {
      if (n >= bits_per_word)
        return (word_t)(word_t(-1) << p);

      word_t x = (word_t)((word_t(1) << n) - word_t(1));
      return (word_t)(x << p);
    }

  #if defined(ERMINE_STD_LIB)
    friend std::ostream& operator<< (std::ostream& stream, bitset& x) {
      for (size_t i = 0; i < S; i++)
        stream << x.test(i);
      return stream;
    }
  #endif
  };
}

// Math
namespace ermine {
  #if !defined(ERMINE_NUMBER_TYPE)
     #define ERMINE_NUMBER_TYPE int
  #endif

  #if !defined(ERMINE_REAL_TYPE)
     #define ERMINE_REAL_TYPE double
  #endif

  #if !defined(ERMINE_REAL_EPSILON)
     #define ERMINE_REAL_EPSILON 0.0001
  #endif

    int req_real_precision(double t) {
      return ((-1 * (int)log10(t)));
    }

    typedef ERMINE_NUMBER_TYPE number_t;                   // Whole number Container.
    typedef ERMINE_REAL_TYPE   real_t;                     // Real number Container.
    const   real_t             real_epsilon(ERMINE_REAL_EPSILON);
    const   int                real_precision = req_real_precision(ERMINE_REAL_EPSILON);

  namespace runtime {
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

    template <typename T>
    constexpr T min(T a, T b) {
      return ((a) < (b) ? (a) : (b));
    }

    template <typename T, typename... Ts>
    static constexpr T min(T a, Ts... bs) {
      return min(a, min(bs...));
    }

    template <typename T>
    constexpr T abs(T a) {
      return ((a) < (T)0 ? -(a) : (a));
    }
  }
}

// Object System Base
namespace ermine {
  namespace memory {
    template <typename T>
    struct pointer {
      T *ptr;

      inline explicit pointer(T *p = nullptr) : ptr(p) { }
      inline operator T* () const { return ptr; }

      inline pointer& operator= (T *other) {
        ptr = other;
        return *this;
      }

      inline T *operator->() const { return ptr; }
    };

    inline size_t align_of(uintptr_t size, size_t align) {
      return (size + align - 1) & ~(align - 1);
    }

    template <class T>
    size_t align_of(const void* ptr) {
      return align_of(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }

    inline size_t align_req(uintptr_t size, size_t align) {
      size_t adjust = align - (size & (align - 1));

      if (adjust == align)
        return 0;
      return adjust;
    }

    template <class T>
    size_t align_req(const void* ptr) {
      return align_req(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }

    template <typename... Ts>
    constexpr size_t max_sizeof() {
      return rt::max(sizeof(Ts)...);
    }
  }

  #ifdef ERMINE_MEMORY_POOL_SIZE
  namespace memory {
    namespace allocator {
      template <typename page_t, size_t pool_size, typename bitset_word_t = ERMINE_BITSET_WORD_TYPE>
      struct memory_pool {
        bitset<pool_size, bitset_word_t> used;
        page_t pool[pool_size];
        size_t next_ptr;

        memory_pool() : pool{0}, next_ptr(0) { }

        inline size_t scan(size_t n_pages, size_t from_page = 0) const {
          for (;;) {
            size_t begin = used.ffr(from_page);
            size_t end = begin + n_pages;

            if (end > pool_size)
              return pool_size;

            if (used.ffs(begin, end) >= end)
              return begin;

            from_page = end;
          }
        }

        void* allocate(size_t req_size) {
          req_size = align_of(req_size, sizeof(page_t)) + sizeof(page_t);
          size_t n_pages = req_size / sizeof(page_t);
          size_t page = scan(n_pages, next_ptr);

          if (page == pool_size) {
            page = scan(n_pages);
            if (page == pool_size)
              return nullptr;
          }

          pool[page] = (page_t)n_pages;
          next_ptr = page + n_pages;
          used.flip(page, next_ptr);

          return &pool[++page];
        }

        void free(void* p) {
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

  namespace memory {
    namespace allocator {
      memory_pool<ERMINE_MEMORY_POOL_PAGE_TYPE, ERMINE_MEMORY_POOL_SIZE> program_memory;

      struct pool {
        static void init() { }

        static inline void* allocate(size_t s) {
          return program_memory.allocate(s);
        }

        template <typename FT>
        static inline void* allocate() { return allocate(sizeof(FT)); }

        static inline void free(void* ptr) { program_memory.free(ptr); }
      };
    }
  }
  #endif

  #ifdef ERMINE_MEMORY_BOEHM_GC

  #define ERMINE_ALLOCATOR memory::allocator::gc
  #define ERMINE_DISABLE_RC true

  #include <gc.h>

  namespace memory {
    namespace allocator {

      struct gc {
        static void init() { GC_INIT(); }

        static inline void* allocate(size_t s) {
  #ifdef ERMINE_DISABLE_MULTI_THREADING
          return GC_MALLOC(s);
  #else
          return GC_MALLOC_ATOMIC(s);
  #endif
        }

        template <typename FT>
        static inline void* allocate() { return allocate(sizeof(FT)); }

        static inline void free(void* ptr) { }
      };
    }
  }
  #endif

  #if !defined(ERMINE_ALLOCATOR)

  #define ERMINE_ALLOCATOR memory::allocator::system

  namespace memory {
    namespace allocator {

      struct system {
        static void init() { }

        static inline void* allocate(size_t s) { return ::malloc(s); }

        template <typename FT>
        static inline void* allocate() { return allocate(sizeof(FT)); }

        static inline void free(void* ptr) { ::free(ptr); }
      };
    }
  }
  #endif

  namespace memory {
    namespace allocator {
      struct synchronized {
        static mutex lock;

        static void init() { ERMINE_ALLOCATOR::init(); }

        static inline void* allocate(size_t s) {
          lock_guard guard(lock);
          return ERMINE_ALLOCATOR::allocate(s);
        }

        template <typename FT>
        static inline void* allocate() { return allocate(sizeof(FT)); }

        static inline void free(void* ptr) {
          lock_guard guard(lock);
          ERMINE_ALLOCATOR::free(ptr);
        }
      };
    }
  }

  #if !defined(ERMINE_DISABLE_MULTI_THREADING)

    #if defined(ERMINE_MEMORY_POOL_SIZE)
      mutex memory::allocator::synchronized::lock;
      #undef ERMINE_ALLOCATOR
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
      struct no_rc {

        inline void inc_ref() { }
        inline bool dec_ref() { return false; }
      };
  #else
      template <typename T>
      struct rc {
        rc() : ref_count(0) { }

        inline void inc_ref() { ref_count++; }
        inline bool dec_ref() { return (--ref_count == 0); }

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

  template <typename>
  void type_id() { }

  using type_id_t = void(*)();
  typedef type_id_t type_t;

  struct var;
  typedef var const & ref;
  struct seekable_i;

  template <typename rc>
  struct object_i : rc {
    object_i() { }
    virtual ~object_i() { };

    virtual type_t type() const = 0;

    virtual bool equals(ref) const;

    virtual seekable_i* cast_seekable_i() { return nullptr; }

    void* operator new(size_t, void* ptr) { return ptr; }
    void  operator delete(void* ptr) { ERMINE_ALLOCATOR::free(ptr); }
  };

  typedef object_i<ERMINE_RC_POLICY> object;

  #if !defined(ERMINE_POINTER_T)
    #define ERMINE_POINTER_T memory::pointer<object>
  #endif

  typedef ERMINE_POINTER_T pointer_t;

  struct var {
    explicit inline var(object* o = nullptr) : obj(o) { inc_ref(); }
    inline var(ref o)   : obj(o.obj) { inc_ref(); }
    inline var(var&& o) : obj(o.detach()) { }

    ~var() { dec_ref(); }

    inline var& operator=(var&& other) {
      if (this != &other) {
        dec_ref();
        obj = other.detach();
      }
      return *this;
    }

    inline var& operator= (ref other) {
      if (obj != other.obj) {
        dec_ref();
        obj = other.obj;
        inc_ref();
      }
      return *this;
    }

    bool equals (ref) const;

    bool operator==(ref other) const { return equals(other); }

    bool operator!=(ref other) const { return !equals(other); }

    void* operator new(size_t, void* ptr) { return ptr; }

    operator bool() const;

    inline object* get() const { return obj; }

    template <typename T>
    inline T* cast() const { return static_cast<T*>((object*)obj); }

    inline bool is_type(type_t type) const {
      if (obj)
        return (static_cast<object*>(obj)->type() == type);
      return false;
    }

    inline bool is_nil() const { return (obj == nullptr); }

    object* detach() {
      object* _obj = obj;
      obj = nullptr;
      return _obj;
    }

    inline void inc_ref() {
  #if !defined(ERMINE_DISABLE_RC)
      // Only change if non-null
      if (obj) obj->inc_ref();
  #endif
    }

    inline void dec_ref() {
  #if !defined(ERMINE_DISABLE_RC)
      // Only change if non-null
      if (obj) {
        // Subtract and test if this was the last pointer.
        if (obj->dec_ref()) {
          delete obj;
          obj = nullptr;
        }
      }
  #endif
    }

    pointer_t obj;
  };

  template <>
  inline seekable_i* var::cast<seekable_i>() const { return obj->cast_seekable_i(); }

  template <typename rc>
  bool object_i<rc>::equals(ref o) const {
    return (this == o.get());
  }

  template <typename FT, typename... Args>
  inline var obj(Args... args) {
    void* storage = ERMINE_ALLOCATOR::allocate<FT>();
    return var(new(storage) FT(args...));
  }

  inline var nil() {
    return var();
  }

  #undef alloca

  template <typename T>
  struct alloca {
    byte memory [sizeof(T)];

    template <typename... Args>
    inline explicit alloca(Args... args) {
      (new(memory) T(args...))->inc_ref();
    }

    inline operator object*() {
      return (object*)memory;
    }
  };
}

namespace ermine {
  template <typename T>
  struct array {
    size_t _size{0};

    T* data {nullptr};

    explicit inline array(size_t s = 0) : _size(s) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
    }

    explicit inline array(const T* source, size_t s = 0) : _size(s) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
      for (size_t i = 0; i < _size; i++)
        data[i] = source[i];
    }

  #if defined(ERMINE_STD_LIB)
    explicit inline array(std::initializer_list<T> source) : _size(source.size()) {
      data = (T *)ERMINE_ALLOCATOR::allocate(_size * sizeof(T));
      size_t idx = 0;
      for (auto item : source) {
        data[idx] = item;
        idx++;
      }
    }
  #endif

    inline array(array&& m) : data(m.data), _size(m.size()) { m.data = nullptr; }

    inline array(array& m) : _size(m.size()) {
      for (size_t i = 0; i < _size; i++)
        data[i] = m.data[i];
    }

    ~array() {
      ERMINE_ALLOCATOR::free(data);
    }


    inline array& operator=(array&& x) {
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }

    inline T& operator [](size_t idx)      { return data[idx]; }
    inline T operator [](size_t idx) const { return data[idx]; }

    inline T*     begin() const { return &data[0];     }
    inline T*     end()   const { return &data[_size]; }
    inline size_t size()  const { return _size;        }
  };
}

// Runtime Prototypes
namespace ermine {
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

  #define for_each(x,xs) for (var _tail_ = rt::rest(xs), x = rt::first(xs); !_tail_.is_nil(); x = rt::first(_tail_), _tail_ = rt::rest(_tail_))

  template <typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args);

  template <typename T>
  inline var run(T const & fn);

  template <>
  inline var run(ref);

  namespace runtime {
    inline var apply(ref fn, ref argv);
  }
}
"
     :native_headers      native-headers
     :objects             objects
     :symbols             symbol-table
     :native_declarations native-declarations
     :ermine_cpp          "
namespace ermine {
  namespace runtime {
    inline bool is_seqable(ref coll) {
      if (coll.cast<seekable_i>())
        return true;
      else
        return false;
    }

    inline var first(ref seq) {
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->first();
    }

    inline var rest(ref seq) {
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->rest();
    }

    inline var cons(ref x, ref seq) {
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return rt::list(x);
      return seq.cast<seekable_i>()->cons(x);
    }

    var nth(var seq, number_t index) {
      if (index < 0)
        return nil();

      for (number_t i = 0; i < index; i++)
        seq = rt::rest(seq);

      return rt::first(seq);
    }

    var nthrest(var seq, number_t index) {
      for (number_t i = 0; i < index; i++)
        seq = rt::rest(seq);

      if (seq.is_nil())
        return rt::list();
      else
        return seq;
    }

    inline size_t count(ref seq) {
      size_t acc = 0;

      for (var tail = rt::rest(seq); !tail.is_nil(); tail = rt::rest(tail))
        acc++;

      return acc;
    }

    inline var range(number_t low, number_t high) {
      struct seq : lambda_i {
        number_t low, high;

        explicit seq(number_t l, number_t h) : low(l), high(h) { }

        var invoke(ref) const final {
          if (low < high)
            return obj<lazy_sequence>(obj<number>(low), obj<seq>((low + 1), high));
          else
            return nil();
        }
      };

      return obj<lazy_sequence>(obj<seq>(low, high));
    }
  }

  template <typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args) {
    return fn.invoke(rt::list(args...));
  }

  template <typename T>
  inline var run(T const & fn) {
    return fn.invoke(nil());
  }

  template <>
  inline var run(ref fn) {
    return fn.cast<lambda_i>()->invoke(nil());
  }

  template <typename... Args>
  inline var run(ref fn, Args const & ... args) {
    return fn.cast<lambda_i>()->invoke(rt::list(args...));
  }

  namespace runtime {
    inline var apply(ref f, ref argv) {
      if (rt::rest(argv).is_type(type_id<empty_sequence>))
        return f.cast<lambda_i>()->invoke(rt::first(argv));

      struct {
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
     :lambda_classes (lambda-definitions lambdas)
     :lambda_bodies  (lambda-implementations lambdas)
     :body           (remove empty? body)
     :ermine_main    main)))

(defn -main [& args]
    (write-file "./main.cpp" (program-template (emit-source (read-ermine "./main.clj")))))
