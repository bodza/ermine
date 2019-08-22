(ns ermine.core
  (:refer-clojure :only [= and apply assoc atom coll? comp concat conj cons count declare defn deref double drop drop-while empty? every? false? filter first flatten fn gensym hash-map hash-set instance? interleave interpose into last let letfn list loop map map-indexed meta nil? not number? odd? or partition pop print read-line read-string reduce remove repeat repeatedly rest second seq seq? some? str string? swap! symbol symbol? take-while true? update vector with-meta  *ns* *print-length* .. intern]) (:require [clojure.core :as -])
  (:require [clojure.set :refer [difference intersection]]
            [clojure.string :refer [escape]]
            [clojure.walk :refer [prewalk]]
            [fast-zip.core :as zip]
            [flatland.ordered.map :refer [ordered-map]]))

(def ermine-runtime '(
  (defn deref [a] "return a.cast<deref_i>()->deref();")

  (defn assoc [m k v] "return m.cast<map_t>()->assoc(k, v);")
  (defn dissoc [m k] "return m.cast<map_t>()->dissoc(k);")

  (defn get [m & args] "return m.cast<map_t>()->val_at(args);")

  (defn vals [m] "return m.cast<map_t>()->vals();")
  (defn keys [m] "return m.cast<map_t>()->keys();")

  (defn atom [x] "return obj<atomic>(x)")

  (defn swap! [a f & args] "return a.cast<atomic>()->swap(f, args);")
  (defn reset! [a x] "return a.cast<atomic>()->reset(x);")

  (defn lazy-seq! [f] "return obj<lazy_sequence>(f);")

  (defn list [& s] "return s;")

  (defn list? [x] "return x.is_type(type_id<sequence>) ? cached::true_o : cached::false_o;")

  (defn seqable? [x] "return runtime::is_seqable(x) ? cached::true_o : cached::false_o;")

  (defn cons [x s] "return runtime::cons(x, s);")

  (defn first [s] "return runtime::first(s);")
  (defn rest [s] "return runtime::rest(s);")

  (defn second [s] (first (rest s)))

  (defn nth [s ^number_t n] "return runtime::nth(s, n);")
  (defn nthrest [s ^number_t n] "return runtime::nthrest(s, n);")

  (defn reduce [f r s]
     "var q = r;

      for_each(i, s)
        q = run(f, q, i);

      return q;")

  (defn apply [f & s] "return runtime::apply(f, s);")

  (defn conj [coll & s] (reduce (fn [h v] (cons v h)) (if (nil? coll) (list) coll) s))

  (defn reverse [s] (reduce (fn [h v] (cons v h)) (list) s))

  (defn true? [x] "return (x) ? cached::true_o : cached::false_o;")
  (defn false? [x] "return (!x) ? cached::true_o : cached::false_o;")

  (defn nil? [x] "return x.is_nil() ? cached::true_o : cached::false_o;")

  (defn not [x] "return (x) ? cached::false_o : cached::true_o;")

  (defn = [& args]
    "var a = runtime::first(args);

     for_each(i, runtime::rest(args)) {
       if (a != i)
         return cached::false_o;
       a = i;
     }

     return cached::true_o;")

  (defn identical? [x y] "return (x.get() == y.get()) ? cached::true_o : cached::false_o;")

  (defn < [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<real_t>(a) >= number::to<real_t>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn > [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<real_t>(a) <= number::to<real_t>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn >= [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<real_t>(a) < number::to<real_t>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn <= [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<real_t>(a) > number::to<real_t>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn count [s] "return obj<number>(runtime::count(s))")

  (defn zero? [x] (= x 0))
  (defn pos? [x] (> x 0))
  (defn neg? [x] (< x 0))

  (defn + [& args]
    "real_t value(0.0);

     for_each(i, args)
       value = value + number::to<real_t>(i);

     return obj<number>(value);")

  (defn - [& args]
    "var a = runtime::first(args);

     real_t value = number::to<real_t>(a);
     size_t count = 1;

     for_each(i, runtime::rest(args)) {
       value = (value - number::to<real_t>(i));
       count++;
     }

     if (count == 1)
       value = value * real_t(-1.0);

     return obj<number>(value);")

  (defn * [& args]
    "real_t value(1.0);

     for_each(i, args)
       value = (value * number::to<real_t>(i));

     return obj<number>(value);")

  (defn inc [x] (+ x 1))
  (defn dec [x] (- x 1))

  (defn min [& args]
    "var m = runtime::first(args);

     for_each(i, runtime::rest(args))
       if (number::to<real_t>(m) > number::to<real_t>(i))
         m = i;

     return m;")

  (defn max [& args]
    "var m = runtime::first(args);

     for_each(i, runtime::rest(args))
       if (number::to<real_t>(m) < number::to<real_t>(i))
         m = i;

     return m;")

  (defn bit-and [^number_t x ^number_t y] "return obj<number>((x & y));")
  (defn bit-not [^number_t x] "return obj<number>(~x);")
  (defn bit-or [^number_t x ^number_t y] "return obj<number>((x | y));")
  (defn bit-xor [^number_t x ^number_t y] "return obj<number>((x ^ y));")

  (defn bit-shift-left [^number_t x ^number_t n] "return obj<number>((x << n));")
  (defn bit-shift-right [^number_t x ^number_t n] "return obj<number>((x >> n));")

  (defn identity [x] x)

  (defn map [f coll]
    (lazy-seq!
      (fn []
        (if (seqable? coll)
          (cons (f (first coll)) (map f (rest coll)))))))

  (defn range [^number_t n] "return runtime::range(0, n)")

  (defn take [n coll]
    (lazy-seq!
      (fn []
        (if (seqable? coll)
          (if (> n 0)
            (cons (first coll) (take (- n 1) (rest coll))))))))

  (defn take-while [pred s]
    (lazy-seq!
      (fn []
        (if (seqable? s)
          (if (pred (first s))
            (cons (first s) (take-while pred (rest s))))))))

  (defn drop [^number_t n coll] "return runtime::nthrest(coll, n);")

  (defn drop-while-aux [pred coll]
    "var s = coll;

     while (run(pred, s))
       s = runtime::rest(s);

     return s;")

  (defn drop-while [pred coll]
    (lazy-seq!
      (fn []
        (drop-while-aux (fn [s] (if (seqable? s) (pred (first s)) false)) coll))))

  (defn concat1 [x]
    (if (seqable? x)
      (cons (first x) (lazy-seq! (fn [] (concat1 (rest x)))))))

  (defn concat [x y]
    (if (seqable? x)
      (cons (first x) (lazy-seq! (fn [] (concat (rest x) y))))
      (concat1 y)))

  (defn filter [pred coll]
    (lazy-seq!
      (fn []
        (if (seqable? coll)
          (let [[f & r] coll]
            (if (pred f)
              (cons f (filter pred r))
              (filter pred r)))))))

  (defn partition [n coll]
    (lazy-seq!
      (fn []
        (if (seqable? coll)
          (let [p (take n coll)]
            (if (= n (count p))
              (cons p (partition n (nthrest coll n)))))))))

  (defn every? [pred coll]
    "for_each(i, coll) {
       if (!run(pred, i))
         return cached::false_o;
     }
     return cached::true_o;")

  (defn interleave [s1 s2]
    (lazy-seq!
      (fn []
        (if (seqable? s1)
          (if (seqable? s2)
            (cons (first s1) (cons (first s2) (interleave (rest s1) (rest s2)))))))))

  (defn flatten [s]
    (lazy-seq!
      (fn []
        (if (seqable? s)
          (if (seqable? (first s))
            (concat (flatten (first s)) (flatten (rest s)))
            (cons (first s) (flatten (rest s))))))))

  (defn string? [s] "return s.is_type(type_id<string>) ? cached::true_o : cached::false_o;")
))

(defn escape-string [s] (escape s (hash-map \" "\\\"", \\ "\\\\")))

(defn form?
  ([s] (fn [f] (form? s f)))
  ([s f] (and (seq? f) (= (first f) s))))

(defn symbol-set [form] (into (hash-set) (filter symbol? (flatten form))))

(defn split-fn [sig]
  (let [name (if (symbol? (second sig)) (second sig) nil)
        sig  (if name (drop 2 sig) (rest sig))
        [args & body] sig]
    [name args body]))

(defn ffi-fn? [body] (and (seq body) (every? true? (map string? body))))

(defn fn-arg-symbol? [s] (and (symbol? s) (not (= s '&)) (not (= s '_))))

(defn transform [tree pred f]
  (prewalk (fn [form]
             (if (pred form)
               (let [new-form (f form)
                     meta (meta form)]
                 (if (and (instance? clojure.lang.IMeta form)
                          (instance? clojure.lang.IMeta new-form))
                   (with-meta new-form meta)
                   new-form))
               form))
           tree))

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

(defn escape-fn-calls [form]
  (transform form
    (fn [f] (and (seq? f) (form? 'ast-fn-heap (first f))))
    (fn [[[_ & fun] & args]] (cons (cons 'ast-fn-stack fun) args))))

(defn escape-fn-inheritance [form]
  (let [heap-fns (into (hash-set) (map second (parser-peek form (form? 'ast-fn-heap))))
        stack-fns (into (hash-set) (map second (parser-peek form (form? 'ast-fn-stack))))
        escapeable-fns (difference stack-fns heap-fns)]
    (transform form
        (fn [f] (and (seq? f) (= (first f) 'ast-defn-heap) (escapeable-fns (second f))))
        (fn [[_ & fun]] (cons 'ast-defn-stack fun)))))

(defn let-closure [bindings body]
  (if (empty? bindings)
    (list (apply list 'fn [] body))
    (if (odd? (count bindings))
      (throw (Error. (str "let requires an even number of forms in binding vector => " bindings)))
      (letfn [(close [[arg val] & more] (list (apply list 'fn [arg] (if (seq more) (list (apply close more)) body)) val))]
        (apply close (partition 2 bindings))))))

(defn fn-made-unique [args body]
  (if (string? (first body))
    (apply list 'ast-lambda args body)
    (let [syms (filter fn-arg-symbol? (flatten args))
          uniq (apply hash-map (interleave syms (map (fn [%] (symbol (str % (gensym "__")))) syms)))]
      (apply list 'ast-lambda (transform args uniq uniq) (transform body uniq uniq)))))

(defn expand-macros [form]
  (let [form (transform form (form? 'defn) (fn [[_ name args & body]] (list 'def name (apply list 'fn args body))))
        form (transform form (form? 'do) (fn [[_ & body]] (apply list 'let [] body)))
        form (transform form (form? 'let) (fn [[_ bindings & body]] (let-closure bindings body)))]
    (transform form (form? 'fn) (fn [[_ args & body]] (fn-made-unique args body)))))

(defn fn-defined? [fns env args body]
  (let [name ((deref fns) (concat [env args] body))]
    (if name
      (apply list 'ast-fn-heap name env))))

(defn define-fn [fns env name args body]
  (let [name (or name (gensym "FN__"))]
    (swap! fns assoc (concat [env args] body) name)
    (apply list 'ast-fn-heap name env)))

(defn fn->lift
  ([form]
   (let [fns  (atom (ordered-map))
         form (fn->lift form fns)
         fns  (map (fn [[body name]] (concat ['ast-defn-heap name] body)) (deref fns))]
     (concat fns form)))
  ([form fns & [env]]
   (transform form (form? 'ast-lambda)
    (fn [sig]
      (let [[name args body] (split-fn sig)
            ;; transform named recursion in body
            body (if name
                   (transform body (form? name) (fn [[_ & args]] (cons (apply list 'ast-fn-heap name env) args)))
                   body)
            body (fn->lift body fns (concat args env))
            symbols (symbol-set body)
            env  (into (list) (intersection symbols (into (hash-set) (flatten env))))
            args (if (ffi-fn? body)
                   args
                   (transform args symbol? (fn [v] (if (or (not (fn-arg-symbol? v)) (symbols v)) v '_))))]
        (or (fn-defined? fns env args body) (define-fn fns env name args body)))))))

(defn escape-cpp-symbol [s]
  (escape (str s) (hash-map \- "_", \* "_star_", \+ "_plus_", \/ "_slash_", \< "_lt_", \> "_gt_", \= "_eq_", \? "_QMARK_", \! "_BANG_", \# "_")))

(defn symbol-conversion [form]
  (transform form symbol? (comp (fn [%] (symbol (escape-cpp-symbol %))) (fn [%] (if (= 'not %) '_not_ %)))))

(defn escape-analysis [form] (escape-fn-inheritance (escape-fn-calls form)))

(defn compile [form]
  (symbol-conversion (escape-analysis (fn->lift (expand-macros (concat ermine-runtime form))))))

(declare emit)

(defn emit-ast [form model] (into (vector) (map (fn [f] (emit f model)) form)))

(defn program-model [form]
  (let [model (atom (hash-map :symbols (hash-set), :lambdas (vector))), program (emit-ast (compile form) model)]
    (assoc (deref model) :program program)))

(defn emit--def [[_ name & form] model]
  (swap! model update :symbols conj name)
  (apply str name " = " (emit-ast form model)))

(defn emit--if [[_ test then else] model]
  (let [test (emit test model)
        then (emit then model)
        else (if (nil? else) "nil()" (emit else model))]
    (apply str "(" test " ? " then " : " else ")")))

(defn emit--list [[_ & args] model] (str "runtime::list(" (apply str (interpose ", " (emit-ast args model))) ")"))

(defn norm-fn-env [env] (remove (fn [%] (or (= % '&) (= % '_))) (flatten env)))

(defn new-fn-heap [[_ name & env]] (str "obj<" name ">(" (apply str (interpose ", " (norm-fn-env env))) ")"))
(defn new-fn-stack [[_ name & env]] (str name "(" (apply str (interpose ", " (norm-fn-env env))) ")"))

(defn invoke-fn [name args] (str "run(" name (if (seq args) (apply str ", " (interpose ", " args)) "") ")"))

(declare destructure-arguments)

(defn destructure-nth-rest [parent i]
  (reduce (fn [h v] (str v "(" h ")")) parent (repeat i "runtime::rest")))

(defn destructure-nth [parent i]
  (str "runtime::first(" (destructure-nth-rest parent i) ")"))

(defn new-fn-arg [name parent i]
  (let [value (destructure-nth parent i)]
    (if (= (:tag (meta name)) 'number_t)
      (str "number_t " name " = number::to<number_t>(" value ")")
      (str "ref " name " = " value))))

(defn new-fn-var-arg [name parent i]
  (str "ref " name " = " (destructure-nth-rest parent i)))

(defn destructure-sequential [args parent]
  (reduce
    (fn [v [i name]]
      (let [name (if (symbol? name)
                   (new-fn-arg name parent i)
                   (if (coll? name)
                     (destructure-arguments name (destructure-nth parent i))))]
        (conj v name))) (vector) args))

(defn destructure-var-args [name parent i]
  (if (nil? name)
    (vector)
    (if (symbol? name)
      (new-fn-var-arg name parent i)
      (if (coll? name)
        (let [tmp# (gensym)]
          (vector (new-fn-var-arg tmp# parent i) (destructure-arguments name tmp#)))))))

(defn destructure-arguments
  ([args] (flatten (destructure-arguments args "_args_")))
  ([args parent]
   (let [t-args       args
         args         (take-while (fn [%] (not (= % '&))) t-args)
         var-args     (second (drop-while (fn [%] (not (= % '&))) t-args))
         args-indexed (remove (fn [%] (= (second %) '_)) (map-indexed (fn [i v] [i v]) args))
         var-args     (destructure-var-args var-args parent (count args))
         args         (destructure-sequential args-indexed parent)]
     (vector args var-args (vector)))))

(defn emit-lambda [name env args body model]
  (let [body (if (empty? body)
               ["return nil()"]
               (if (ffi-fn? body)
                 (let [body (apply str body)]
                   (if (.contains body "return") [body] [body "return nil()"]))
                 (let [body (emit-ast body model)]
                   (conj (pop body) (str "return " (last body))))))
        env  (norm-fn-env env)
        vars (destructure-arguments args)]
    (hash-map :name name :env env :args args :vars vars :body body)))

(defn emit--defn-heap [[_ name env args & body] model] (swap! model update :lambdas conj (emit-lambda name env args body model)) "")
(defn emit--defn-stack [[_ name env args & body] model] (swap! model update :lambdas conj (assoc (emit-lambda name env args body model) :stack true)) "")

(defn emit [f m]
  (if (form? 'ast_defn_heap f)  (emit--defn-heap f m)
    (if (form? 'ast_defn_stack f) (emit--defn-stack f m)
      (if (form? 'ast_fn_heap f)    (new-fn-heap f)
        (if (form? 'ast_fn_stack f)   (new-fn-stack f)
          (if (form? 'list f)           (emit--list f m)
            (if (form? 'if f)             (emit--if f m)
              (if (form? 'def f)            (emit--def f m)
                (if (symbol? f)               (str f)
                  (if (number? f)               (str "obj<number>(" (double f) ")")
                    (if (nil? f)                  "nil()"
                      (if (string? f)               (str "obj<string>(\"" (escape-string f) "\", " (count f) ")")
                        (if (or (true? f) (false? f)) (if (true? f) "cached::true_o" "cached::false_o")
                          (if (seq? f)                  (let [[fun & args] f] (invoke-fn (emit fun m) (emit-ast args m)))
                                                          (throw (Error. (str "unsupported form => " f)))))))))))))))))

(defn source-string [source]
  (str
"
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
      else
        return adjust;
    }

    template <class T>
    size_t align_req(const void* ptr) {
      return align_req(reinterpret_cast<uintptr_t>(ptr), sizeof(T));
    }

    template <typename... Ts>
    constexpr size_t max_sizeof() {
      return runtime::max(sizeof(Ts)...);
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
    pointer_t obj;

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
      else
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

  #define for_each(x,xs) for (var _tail_ = runtime::rest(xs), x = runtime::first(xs); !_tail_.is_nil(); x = runtime::first(_tail_), _tail_ = runtime::rest(_tail_))

  template <typename T, typename... Args>
  inline var run(T const & fun, Args const & ... args);

  template <typename T>
  inline var run(T const & fun);

  template <>
  inline var run(ref);

  namespace runtime {
    inline var apply(ref fun, ref args);
  }
}

// Objects
namespace ermine {
  struct seekable_i {
    virtual var cons(ref x) = 0;
    virtual var first() = 0;
    virtual var rest() = 0;

    static bool equals(var lhs, var rhs) {
      for ( ; ; lhs = runtime::rest(lhs), rhs = runtime::rest(rhs)) {
        ref lf = runtime::first(lhs);
        ref rf = runtime::first(rhs);

        if (lf.is_nil() && rf.is_nil())
          return true;

        if (lf != rf)
          return false;
      }
    }
  };

  struct lambda_i : object {
    type_t type() const { return type_id<lambda_i>; }

    virtual var invoke(ref args) const = 0;
  };

  struct deref_i : object {
    virtual var deref() = 0;
  };

  struct boolean final : object {
    type_t type() const final { return type_id<boolean>; }

    const bool value;

    explicit boolean(bool b) : value(b) { }

    bool container() const {
      return value;
    }

    bool equals(ref o) const final {
      return (value == o.cast<boolean>()->container());
    }
  };

  namespace cached {
    const var true_o = obj<::ermine::boolean>(true);
    const var false_o = obj<::ermine::boolean>(false);
  }

  var::operator bool() const {
    if (obj == nullptr)
      return false;
    else if (obj->type() == (type_t)type_id<boolean>)
      return cast<boolean>()->container();
    else
      return true;
  }

  bool var::equals(ref o) const {
    if (get() == o.get())
      return true;
    else if (is_nil() || o.is_nil())
      return false;
    else if (runtime::is_seqable(*this) && runtime::is_seqable(o))
      return seekable_i::equals(*this, o);
    else if (obj->type() != o.get()->type())
      return false;
    else
      return get()->equals(o);
  }

  template <typename T>
  struct value final : object {
    type_t type() const final { return type_id<value>; }

    T payload;

    template <typename... Args>
    explicit value(Args&&... args) : payload(static_cast<Args&&>(args)...) { }

    T to_value() const {
      return payload;
    }

    static T to_value(ref v) {
      return v.cast<value<T>>()->payload;
    }

    T& to_reference() {
      return payload;
    }

    static T& to_reference(ref v) {
      return v.cast<value<T>>()->to_reference();
    }
  };

  struct number final : object {
    type_t type() const final { return type_id<number>; }

    const real_t n;

    template <typename T> explicit number(T x) : n(real_t(x)) { }

    bool equals(ref o) const final {
      return (runtime::abs(n - number::to<real_t>(o)) < real_epsilon);
    }

    template <typename T> static T to(ref v) {
      return (T)v.cast<number>()->n;
    }
  };

  struct empty_sequence final : object {
    type_t type() const final { return type_id<empty_sequence>; }
  };

  namespace cached {
    const var empty_sequence_o = obj<::ermine::empty_sequence>();
  }

  struct sequence final : object, seekable_i {
    type_t type() const final { return type_id<sequence>; }

    const var next;
    const var data;

    explicit sequence(ref d = nil(), ref n = nil()) : next(n), data(d) { }

    virtual seekable_i* cast_seekable_i() { return this; }

    var cons(ref x) final {
      return obj<sequence>(x, var(this));
    }

    var first() final {
      return data;
    }

    var rest() final {
      return next;
    }

    template <typename T> static T to(ref) {
      T::unimplemented_function;
    }

    template <typename T> static var from(T) {
      T::unimplemented_function;
      return nil();
    }
  };

  namespace runtime {
    inline var list() {
      return cached::empty_sequence_o;
    }

    inline var list(ref v) {
      return obj<sequence>(v, cached::empty_sequence_o);
    }

    template <typename... Args>
    inline var list(ref first, Args const & ... args) {
      return obj<sequence>(first, list(args...));
    }
  }

  #ifdef ERMINE_STD_LIB
  typedef ::std::vector<var> std_vector;

  template <> std_vector sequence::to(ref v) {
    std_vector ret;
    for_each(i, v)
      ret.push_back(i);
    return ret;
  }

  template <> var sequence::from(std_vector v) {
    var ret;
    std::vector<var>::reverse_iterator rit;
    for (rit = v.rbegin(); rit != v.rend(); rit++)
      ret = runtime::cons(*rit, ret);
    return ret;
  }
  #endif

  struct lazy_sequence final : object, seekable_i {
    type_t type() const final { return type_id<lazy_sequence>; }

    mutex lock;
    bool cache;
    var thunk;
    var data;
    var seq;

    explicit lazy_sequence(ref t, bool c = false) : cache(c), thunk(t) { }

    explicit lazy_sequence(ref d, ref t, bool c = false) : cache(c), thunk(t), data(d) { }

    virtual seekable_i* cast_seekable_i() { return this; }

    void yield() {
      if (thunk.is_nil())
        return;

      seq = run(thunk);

      if (data.is_nil()) {
        data = runtime::first(seq);
        seq = runtime::rest(seq);
      }

      thunk = nil();
    }

    var cons(ref x) final {
      lock_guard guard(lock);

      if (data.is_nil())
        return obj<lazy_sequence>(x, thunk, cache);

      return obj<sequence>(x, var((object*)this));
    }

    var first() final {
      lock_guard guard(lock);

      if (cache)
        yield();
      else if (data.is_nil())
        return runtime::first(run(thunk));

      return data;
    }

    var rest() final {
      lock_guard guard(lock);
      var tail;

      if (cache) {
        yield();
        tail = seq;
      } else {
        tail = run(thunk);
        if (data.is_nil())
          return runtime::rest(tail);
      }

      if (tail.is_nil())
        return runtime::list();
      else
        return tail;
    }
  };

  template <typename element_t, typename object_t>
  struct array_seq : object, seekable_i {
    type_t type() const final { return type_id<array_seq>; }

    typedef array<element_t> array_t;
    typedef value<array_t> value_t;

    size_t pos;
    var storage;

    explicit array_seq(const element_t* src, size_t s = 0) : pos (0), storage(obj<value_t>(src, s)) { }

    explicit array_seq(var b, size_t p = 0) : pos(p), storage(b) { }

    explicit array_seq(size_t size) : pos(0), storage(obj<value_t>(size)) { }

    virtual seekable_i* cast_seekable_i() { return this; }

    var cons(ref x) final {
      return obj<sequence>(x, var(this));
    }

    var first() final {
      array_t& b = value_t::to_reference(storage);

      return obj<object_t>(b[pos]);
    }

    var rest() final {
      array_t& b = value_t::to_reference(storage);

      if (pos < b.size() - 1)
        return obj<array_seq>(storage, pos + 1);
      else
        return runtime::list();
    }
  };

  template <>
  struct array<var> {
    size_t _size {0};

    var* allocate() {
      var* storage = static_cast<var*>(ERMINE_ALLOCATOR::allocate(_size * sizeof(var))) ;
      for (size_t i = 0; i < _size; i++)
        new (&storage[i]) var();
      return storage;
    }

    var* data { nullptr };

    explicit inline array(size_t s = 0) : _size(s), data(allocate()) { }

    inline array(array&& m) : _size(m.size()), data(m.data) { m.data = nullptr; }

    inline array(array& m) : _size(m.size()), data(allocate()) {
      for (size_t i = 0; i < _size; i++)
        data[i] = m.data[i];
    }

    ~array() {
      for (size_t i = 0; i < size(); i++)
        (&data[i])->~var();
      ERMINE_ALLOCATOR::free(data);
    }

    inline array& operator= (array&& x) {
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }

    inline var& operator[] (size_t idx)      { return data[idx]; }
    inline var operator[] (size_t idx) const { return data[idx]; }

    inline var*   begin() const { return &data[0];     }
    inline var*   end()   const { return &data[_size]; }
    inline size_t size()  const { return _size;        }
  };

  typedef array<var> var_array_t;
  typedef value<var_array_t> var_array;
  typedef array_seq<var,var> var_array_seq;

  template <>
  struct array_seq<var,var> : object, seekable_i {
    type_t type() const final { return type_id<array_seq>; }

    size_t pos {0};

    inline static void into_aux(ref) { }

    template <typename... Args>
    inline static void into_aux(ref arr, ref first, Args... rest) {
      auto& data = var_array::to_reference(arr);
      data[data.size() - sizeof...(rest) - 1] = first;
      into_aux(arr, rest...);
    }

    var storage;

    explicit array_seq(var b, size_t p = 0) : pos(p), storage(b) { }

    virtual seekable_i* cast_seekable_i() { return this; }

    var cons(ref x) final {
      return obj<sequence>(x, var(this));
    }

    var first() final {
      var_array_t& b = var_array::to_reference(storage);

      return b[pos];
    }

    var rest() final {
      var_array_t& b = var_array::to_reference(storage);

      if (pos < b.size() - 1)
        return obj<array_seq>(storage, pos + 1);
      else
        return runtime::list();
    }

    template <typename... Args>
    static inline var into(Args... rest) {
      var arr = obj<var_array>(sizeof...(rest));
      into_aux(arr, rest...);
      return obj<var_array_seq>(arr);
    }
  };

  namespace runtime {
    template <typename... Args>
    static inline var dense_list(Args... rest) {
      return var_array_seq::into(rest...);
    }
  }

  struct d_list final : lambda_i, seekable_i {
    type_t type() const final { return type_id<d_list>; }

    var data;

    explicit d_list() : data(runtime::list(runtime::list())) { }

    explicit d_list(ref l) : data(l) { }

    var assoc(ref k, ref v) const {
      ref map = dissoc_aux(k);
      ref _keys = runtime::first(map);
      ref _values = runtime::rest(map);

      return obj<d_list>(runtime::cons(runtime::cons(k, _keys), runtime::cons(v, _values)));
    }

    var dissoc_aux(ref k) const {
      ref _keys = runtime::first(data);
      var _values = runtime::rest(data);

      var new_keys;
      var new_values;

      for_each(i, _keys) {
        if (i != k)
        {
          new_keys = runtime::cons(i, new_keys);
          new_values = runtime::cons(runtime::first(_values), new_values);
          _values = runtime::rest(_values);
        }
      }

      return runtime::cons(new_keys, new_values);
    }

    var dissoc(ref k) const {
      return obj<d_list>(dissoc_aux(k));
    }

    var val_at(ref args) const {
      ref key = runtime::first(args);
      ref not_found = runtime::first(runtime::rest(args));

      ref _keys = runtime::first(data);
      var _values = runtime::rest(data);

      for_each(i, _keys) {
        if (key == i)
          return runtime::first(_values);

        _values = runtime::rest(_values);
      }

      if (!not_found.is_nil())
        return not_found;
      else
        return nil();
    }

    var invoke(ref args) const final {
      return val_at(args);
    }

    var vals() const { return runtime::rest(data); }
    var keys() const { return runtime::first(data); }

    virtual seekable_i* cast_seekable_i() { return this; }

    var cons(ref v) final {
      return runtime::list(v, data);
    }

    var first() final {
      ref _keys = runtime::first(data);
      ref _values = runtime::rest(data);

      return runtime::list(runtime::first(_keys), runtime::first(_values));
    }

    var rest() final {
      ref _keys = runtime::first(data);
      ref _values = runtime::rest(data);

      if (runtime::rest(_keys).is_type(type_id<empty_sequence>))
        return runtime::list();
      else
        return obj<d_list>(runtime::cons(runtime::rest(_keys), runtime::rest(_values)));
    }
  };

  template <>
  inline var obj<d_list>(var keys, var vals) {
    void* storage = ERMINE_ALLOCATOR::allocate<d_list>();

    return var(new(storage) d_list(runtime::cons(keys, vals)));
  }

  #if !defined(ERMINE_MAP_TYPE)
  typedef d_list map_t;
  #endif

  struct string final : object, seekable_i {
    type_t type() const final { return type_id<string>; }

    typedef array_seq<byte, number> array_seq_t;
    typedef array<byte> array_t;

    var data;

    void from_char_pointer(const char* str, int length) {
      data = obj<array_seq_t>((byte*)str, (size_t)(length + 1));

      var seq = (data.cast<array_seq_t>()->storage);
      auto & arr = value<array_t>::to_reference(seq).data;
      arr[length] = 0;
    }

    explicit string() : data(runtime::list()) { }

    explicit string(ref s) : data(s) { }

    explicit string(const char* str) {
      int length;
      for (length = 0; str[length] != 0; ++length)
        ;
      from_char_pointer(str, length);
    }

    explicit string(const char* str, number_t length) { from_char_pointer(str, length); }

    virtual seekable_i* cast_seekable_i() { return this; }

    var cons(ref x) final {
      return obj<string>(runtime::cons(x, data));
    }

    var first() final {
      return runtime::first(data);
    }

    var rest() final {
      ref r = runtime::rest(data);

      if (r.is_type(type_id<array_seq_t>) && runtime::first(r) == obj<number>(0))
        return runtime::list();
      else if (!r.is_type(type_id<empty_sequence>))
        return obj<string>(r);
      else
        return runtime::list();
    }

    static var pack(ref s) {
      if (s.cast<string>()->data.is_type(type_id<array_seq_t>))
        return s.cast<string>()->data;

      size_t size = runtime::count(s);
      var packed_array = obj<value<array_t>>(size + 1);
      auto& packed_data = value<array_t>::to_reference(packed_array).data;

      size_t pos = 0;
      for_each(c, s) {
        packed_data[pos] = number::to<byte>(c);
        pos++;
      }
      packed_data[pos] = 0;

      return obj<array_seq_t>(packed_array);
    }

    static char* c_str(ref s) {
      var seq = (s.cast<array_seq_t>()->storage);
      auto& str = value<array<byte>>::to_reference(seq).data;
      return (char*) str;
    }

    template <typename T> static T to(ref) { T::unimplemented_function; }
  };

  #ifdef ERMINE_STD_LIB
  template <>
  inline var obj<string>(std::string s) {
    void* storage = ERMINE_ALLOCATOR::allocate<string>();
    return var(new(storage) string(s.c_str(), (number_t)s.size()));
  }

  template <> ::std::string string::to(ref str) {
    var packed = string::pack(str);
    return std::string(string::c_str(packed));
  }
  #endif

  struct atomic final : deref_i {
    type_t type() const final { return type_id<atomic>; }

    mutex lock;
    var data;

    explicit atomic(ref d) : data(d) { }

    var swap(ref f, ref args) {
      lock_guard guard(lock);
      data = f.cast<lambda_i>()->invoke(runtime::cons(data, args));
      return data;
    }

    var reset(ref newval) {
      lock_guard guard(lock);
      data = newval;
      return data;
    }

    var deref() final {
      lock_guard guard(lock);
      return data;
    }
  };
}

// Symbols
namespace _main {
  using namespace ermine;

"
    (apply str (interpose "\n" (map (fn [%] (str "  var " % ";")) (:symbols source))))
"
}

// Runtime Implementations
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
      else
        return seq.cast<seekable_i>()->first();
    }

    inline var rest(ref seq) {
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      else
        return seq.cast<seekable_i>()->rest();
    }

    inline var cons(ref x, ref seq) {
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return runtime::list(x);
      else
        return seq.cast<seekable_i>()->cons(x);
    }

    var nth(var seq, number_t index) {
      if (index < 0)
        return nil();

      for (number_t i = 0; i < index; i++)
        seq = runtime::rest(seq);

      return runtime::first(seq);
    }

    var nthrest(var seq, number_t index) {
      for (number_t i = 0; i < index; i++)
        seq = runtime::rest(seq);

      if (seq.is_nil())
        return runtime::list();
      else
        return seq;
    }

    inline size_t count(ref seq) {
      size_t acc = 0;

      for (var tail = runtime::rest(seq); !tail.is_nil(); tail = runtime::rest(tail))
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
  inline var run(T const & fun, Args const & ... args) {
    return fun.invoke(runtime::list(args...));
  }

  template <typename T>
  inline var run(T const & fun) {
    return fun.invoke(nil());
  }

  template <>
  inline var run(ref fun) {
    return fun.cast<lambda_i>()->invoke(nil());
  }

  template <typename... Args>
  inline var run(ref fun, Args const & ... args) {
    return fun.cast<lambda_i>()->invoke(runtime::list(args...));
  }

  namespace runtime {
    inline var apply(ref f, ref args) {
      if (runtime::rest(args).is_type(type_id<empty_sequence>))
        return f.cast<lambda_i>()->invoke(runtime::first(args));

      struct {
        var operator()(ref seq) const {
          ref head = runtime::first(seq);

          if (head.is_nil())
            return cached::empty_sequence_o;

          if (head.cast<seekable_i>())
            return head;

          return runtime::cons(head, (*this)(runtime::rest(seq)));
        }
      } spread;

      return f.cast<lambda_i>()->invoke(spread(args));
    }
  }
}

namespace _main {
"
    (apply str (map (fn [f] (str
"
  struct " (:name f) " " (if (not (:stack f)) "final : lambda_i") " {
"
      (if (seq (:env f)) (str
        (apply str (interpose "\n" (map (fn [%] (str "    const var " % ";")) (:env f))))
"
    explicit " (:name f) " (" (apply str (interpose ", " (map (fn [%] (str "ref " %)) (:env f)))) ") : "
                              (apply str (interpose ", " (map (fn [%] (str % "(" % ")")) (:env f)))) " { }
"
      ))
"
    var invoke (ref _args_) const " (if (not (:stack f)) "final") ";
  };
"
      )) (:lambdas source)))

    (apply str (map (fn [f] (str
"
  inline var " (:name f) "::invoke (ref _args_) const {
    (void)(_args_);
"
      (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (:vars f))))
      (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (:body f))))
"
  }
"
      )) (:lambdas source)))
"

  void main() {
"
    (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (remove empty? (:program source)))))
"
  }
}

int main() {
  using namespace ermine;
  ERMINE_ALLOCATOR::init();

  _main::main();

  return 0;
}
"))

(defn -main [& args]
    (print (source-string (program-model (read-string (str "(" (apply str (interleave (take-while some? (repeatedly read-line)) (repeat "\n"))) ")"))))))
