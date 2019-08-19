(ns compiler.parser
  (:refer-clojure :exclude [drop peek])
  (:gen-class)
  (:require [compiler.io :as io]
            [fast-zip.core :as zip]
            [clojure.walk :as walk]))

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
        sig  (if name (clojure.core/drop 2 sig) (rest sig))
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

(defn drop [tree pred]
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

(defn peek [tree pred & [node-fn]]
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
