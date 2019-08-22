(ns ermine.core
  (:refer-clojure :only [= and apply assoc atom coll? comp concat conj cons count declare defn deref drop drop-while empty? every? false? filter first flatten fn gensym hash-map hash-set instance? int interleave interpose into last let letfn list loop map map-indexed meta nil? not number? odd? or partition pop print read-line read-string reduce remove repeat repeatedly rest second seq seq? some? str string? swap! symbol symbol? take-while true? update vector with-meta  *ns* *print-length* .. intern]) (:require [clojure.core :as -])
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

  (defn nth [s ^int n] "return runtime::nth(s, n);")
  (defn nthrest [s ^int n] "return runtime::nthrest(s, n);")

  (defn reduce [f r s]
     "var q = r;

      for_each(i, s)
        q = run(f, q, i);

      return q;")

  (defn apply [f & s] "return runtime::apply(f, s);")

  (defn conj [coll & s] (reduce (fn [h v] (cons v h)) (if (nil? coll) (list) coll) s))

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
       if (number::to<int>(a) >= number::to<int>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn > [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<int>(a) <= number::to<int>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn >= [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<int>(a) < number::to<int>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn <= [& args]
    "var a = runtime::first(args);

     for_each(b, runtime::rest(args)) {
       if (number::to<int>(a) > number::to<int>(b))
         return cached::false_o;
       a = b;
     }

     return cached::true_o;")

  (defn count [s] "return obj<number>(runtime::count(s))")

  (defn zero? [x] (= x 0))
  (defn pos? [x] (> x 0))
  (defn neg? [x] (< x 0))

  (defn + [& args]
    "int value(0);

     for_each(i, args)
       value = value + number::to<int>(i);

     return obj<number>(value);")

  (defn - [& args]
    "var a = runtime::first(args);

     int value = number::to<int>(a);
     size_t count = 1;

     for_each(i, runtime::rest(args)) {
       value = (value - number::to<int>(i));
       count++;
     }

     if (count == 1)
       value = value * int(-1);

     return obj<number>(value);")

  (defn * [& args]
    "int value(1);

     for_each(i, args)
       value = (value * number::to<int>(i));

     return obj<number>(value);")

  (defn inc [x] (+ x 1))
  (defn dec [x] (- x 1))

  (defn bit-and [^int x ^int y] "return obj<number>((x & y));")
  (defn bit-or [^int x ^int y] "return obj<number>((x | y));")
  (defn bit-xor [^int x ^int y] "return obj<number>((x ^ y));")

  (defn bit-not [^int x] "return obj<number>(~x);")

  (defn bit-shift-left [^int x ^int n] "return obj<number>((x << n));")
  (defn bit-shift-right [^int x ^int n] "return obj<number>((x >> n));")

  (defn identity [x] x)

  (defn map [f coll]
    (lazy-seq!
      (fn []
        (if (seqable? coll)
          (cons (f (first coll)) (map f (rest coll)))))))

  (defn range [^int n] "return runtime::range(0, n)")

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

  (defn drop [^int n coll] "return runtime::nthrest(coll, n);")

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
      (str "int " name " = number::to<int>(" value ")")
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
                  (if (number? f)               (str "obj<number>(" (int f) ")")
                    (if (nil? f)                  "nil()"
                      (if (string? f)               (str "obj<string>(\"" (escape-string f) "\", " (count f) ")")
                        (if (or (true? f) (false? f)) (if (true? f) "cached::true_o" "cached::false_o")
                          (if (seq? f)                  (let [[fun & args] f] (invoke-fn (emit fun m) (emit-ast args m)))
                                                          (throw (Error. (str "unsupported form => " f)))))))))))))))))

(defn source-string [source]
  (str
"
#include <cstdio>
#include <atomic>
#include <mutex>

namespace ermine {
  // Types
  typedef uint8_t byte;

  // Concurrency
  struct mutex {
    ::std::mutex m;

    void lock()   { m.lock();   }
    void unlock() { m.unlock(); }
  };

  struct lock_guard {
    mutex & _ref;

    explicit lock_guard(const lock_guard &) = delete;
    explicit lock_guard(mutex & m) : _ref(m) { _ref.lock(); };
    ~lock_guard() { _ref.unlock(); }
  };
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

    static mutex lock;

    static inline void* allocate(size_t s) {
      lock_guard _(lock);
      return ::malloc(s);
    }

    template <typename FT>
    static inline void* allocate() { return allocate(sizeof(FT)); }

    static inline void free(void* ptr) {
      lock_guard _(lock);
      ::free(ptr);
    }

    template <typename T>
    struct rc {
      T ref_count;

      rc() : ref_count(0) { }

      inline void inc_ref() { ref_count++; }
      inline bool dec_ref() { return (--ref_count == 0); }
    };
  }

  template <typename>
  void type_id() { }

  using type_id_t = void(*)();
  typedef type_id_t type_t;

  struct var;
  typedef var const & ref;
  struct seekable_i;

  template <typename RC>
  struct object_i : RC {
    object_i() { }
    virtual ~object_i() { };

    virtual type_t type() const = 0;

    virtual bool equals(ref) const;

    virtual seekable_i* cast_seekable_i() { return nullptr; }

    void* operator new(size_t, void* ptr) { return ptr; }
    void  operator delete(void* ptr) { memory::free(ptr); }
  };

  typedef object_i<memory::rc<::std::atomic<unsigned int>>> object;

  typedef memory::pointer<object> pointer_t;

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
      // Only change if non-null
      if (obj) obj->inc_ref();
    }

    inline void dec_ref() {
      // Only change if non-null
      if (obj) {
        // Subtract and test if this was the last pointer.
        if (obj->dec_ref()) {
          delete obj;
          obj = nullptr;
        }
      }
    }
  };

  template <>
  inline seekable_i* var::cast<seekable_i>() const { return obj->cast_seekable_i(); }

  template <typename RC>
  bool object_i<RC>::equals(ref o) const {
    return (this == o.get());
  }

  template <typename FT, typename... Args>
  inline var obj(Args... args) {
    void* storage = memory::allocate<FT>();

    return var(new(storage) FT(args...));
  }

  inline var nil() {
    return var();
  }
}

namespace ermine {
  template <typename T>
  struct array {
    size_t _size{0};

    T* data {nullptr};

    explicit inline array(size_t s = 0) : _size(s) {
      data = (T *)memory::allocate(_size * sizeof(T));
    }

    explicit inline array(const T* source, size_t s = 0) : _size(s) {
      data = (T *)memory::allocate(_size * sizeof(T));
      for (size_t i = 0; i < _size; i++)
        data[i] = source[i];
    }

    explicit inline array(std::initializer_list<T> source) : _size(source.size()) {
      data = (T *)memory::allocate(_size * sizeof(T));
      size_t i = 0;
      for (auto item : source) {
        data[i] = item;
        i++;
      }
    }

    inline array(array&& m) : data(m.data), _size(m.size()) { m.data = nullptr; }

    inline array(array& m) : _size(m.size()) {
      for (size_t i = 0; i < _size; i++)
        data[i] = m.data[i];
    }

    ~array() {
      memory::free(data);
    }


    inline array& operator=(array&& x) {
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }

    inline T& operator [](size_t i)      { return data[i]; }
    inline T operator [](size_t i) const { return data[i]; }

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

      var nth(var seq, int index);
      var nthrest(var seq, int index);

      inline size_t count(ref seq);

      inline var range(int low, int high);
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

    const int n;

    template <typename T> explicit number(T x) : n(int(x)) { }

    bool equals(ref o) const final {
      return (n == number::to<int>(o));
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
      lock_guard _(lock);

      if (data.is_nil())
        return obj<lazy_sequence>(x, thunk, cache);

      return obj<sequence>(x, var((object*)this));
    }

    var first() final {
      lock_guard _(lock);

      if (cache)
        yield();
      else if (data.is_nil())
        return runtime::first(run(thunk));

      return data;
    }

    var rest() final {
      lock_guard _(lock);
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
      var* storage = static_cast<var*>(memory::allocate(_size * sizeof(var))) ;
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
      memory::free(data);
    }

    inline array& operator= (array&& x) {
      data = x.data;
      _size = x._size;
      x.data = nullptr;
      return *this;
    }

    inline var& operator[] (size_t i)      { return data[i]; }
    inline var operator[] (size_t i) const { return data[i]; }

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
    void* storage = memory::allocate<d_list>();

    return var(new(storage) d_list(runtime::cons(keys, vals)));
  }

  typedef d_list map_t;

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

    explicit string(const char* str, int length) { from_char_pointer(str, length); }

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

  template <>
  inline var obj<string>(std::string s) {
    void* storage = memory::allocate<string>();

    return var(new(storage) string(s.c_str(), (int)s.size()));
  }

  template <>
  ::std::string string::to(ref str) {
    var packed = string::pack(str);
    return std::string(string::c_str(packed));
  }

  struct atomic final : deref_i {
    type_t type() const final { return type_id<atomic>; }

    mutex lock;
    var data;

    explicit atomic(ref d) : data(d) { }

    var swap(ref f, ref args) {
      lock_guard _(lock);
      data = f.cast<lambda_i>()->invoke(runtime::cons(data, args));
      return data;
    }

    var reset(ref newval) {
      lock_guard _(lock);
      data = newval;
      return data;
    }

    var deref() final {
      lock_guard _(lock);
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

    var nth(var seq, int index) {
      if (index < 0)
        return nil();

      for (int i = 0; i < index; i++)
        seq = runtime::rest(seq);

      return runtime::first(seq);
    }

    var nthrest(var seq, int index) {
      for (int i = 0; i < index; i++)
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

    inline var range(int low, int high) {
      struct seq : lambda_i {
        int low, high;

        explicit seq(int l, int h) : low(l), high(h) { }

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

  int main() {
"
    (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (remove empty? (:program source)))))
"
    return 0;
  }
}

int main() {
  return _main::main();
}
"))

(defn -main [& args]
    (print (source-string (program-model (read-string (str "(" (apply str (interleave (take-while some? (repeatedly read-line)) (repeat "\n"))) ")"))))))
