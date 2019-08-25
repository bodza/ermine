(ns ermine.core
  (:refer-clojure :only [= and apply assoc atom boolean? coll? concat conj cons count declare defn deref doall drop-while empty? every? filter first flatten fn gensym hash-map hash-set int into interleave interpose let letfn list map nil? not number? odd? or partition peek pop print range read-line read-string reduce remove repeat repeatedly rest reverse second seq seq? some? str string? swap! symbol symbol? take-while update  *ns* *print-length* .. intern]) (:require [clojure.core :as -])
  (:require [clojure.string :refer [escape]]
            [clojure.walk :refer [prewalk]]
            [flatland.ordered.map :refer [ordered-map]]))

(def ermine-runtime '(
  (defn assoc [m k v] "return m.cast<Map>()->assoc(k, v)")
  (defn dissoc [m k] "return m.cast<Map>()->dissoc(k)")

  (defn get [m & args] "return m.cast<Map>()->val_at(args)")

  (defn vals [m] "return m.cast<Map>()->vals()")
  (defn keys [m] "return m.cast<Map>()->keys()")

  (defn atom [x] "return obj<Atom>(x)")

  (defn swap! [a f & args] "return a.cast<Atom>()->swap(f, args)")
  (defn reset! [a x] "return a.cast<Atom>()->reset(x)")
  (defn deref [a] "return a.cast<Atom>()->deref()")

  (defn lazy-seq! [f] "return obj<LazySeq>(f)")

  (defn list [& s] "return s")

  (defn list? [x] "return x.is_type(type_id<Cons>) ? cached::true_o : cached::false_o")

  (defn sequence? [x] "return _is_sequence(x) ? cached::true_o : cached::false_o")

  (defn cons [x s] "return _cons(x, s)")

  (defn first [s] "return _first(s)")
  (defn rest [s] "return _rest(s)")

  (defn nth [s n] "return _nth(s, Number::unbox(n))")
  (defn nthrest [s n] "return _nthrest(s, Number::unbox(n))")

  (defn reduce [f r s]
     "Var q = r;

      for (Var x = _first(s), z = _rest(s); !z.is_nil(); x = _first(z), z = _rest(z))
        q = _call(f, q, x);

      return q")

  (defn apply [f & s] "return _apply(f, s)")

  (defn nil? [x] "return x.is_nil() ? cached::true_o : cached::false_o")

  (defn not [x] "return (x) ? cached::false_o : cached::true_o")

  (defn = [a b] "return (a == b) ? cached::true_o : cached::false_o")

  (defn identical? [x y] "return (x.obj == y.obj) ? cached::true_o : cached::false_o")

  (defn < [a b] "return (Number::unbox(a) < Number::unbox(b)) ? cached::true_o : cached::false_o")
  (defn <= [a b] "return (Number::unbox(a) <= Number::unbox(b)) ? cached::true_o : cached::false_o")
  (defn > [a b] "return (Number::unbox(a) > Number::unbox(b)) ? cached::true_o : cached::false_o")
  (defn >= [a b] "return (Number::unbox(a) >= Number::unbox(b)) ? cached::true_o : cached::false_o")

  (defn count [s] "return obj<Number>(_count(s))")

  (defn zero? [x] (= x 0))
  (defn pos? [x] (> x 0))
  (defn neg? [x] (< x 0))

  (defn + [& args]
    "int value(0);

     for (Var i = _first(args), z = _rest(args); !z.is_nil(); i = _first(z), z = _rest(z))
       value = value + Number::unbox(i);

     return obj<Number>(value)")

  (defn - [& args]
    "Var a = _first(args);
     Var s = _rest(args);

     int value = Number::unbox(a);
     size_t count = 1;

     for (Var i = _first(s), z = _rest(s); !z.is_nil(); i = _first(z), z = _rest(z)) {
       value = (value - Number::unbox(i));
       count++;
     }

     if (count == 1)
       value = -value;

     return obj<Number>(value)")

  (defn * [& args]
    "int value(1);

     for (Var i = _first(args), z = _rest(args); !z.is_nil(); i = _first(z), z = _rest(z))
       value = (value * Number::unbox(i));

     return obj<Number>(value)")

  (defn inc [x] (+ x 1))
  (defn dec [x] (- x 1))

  (defn bit-and [x y] "return obj<Number>(Number::unbox(x) & Number::unbox(y))")
  (defn bit-or [x y] "return obj<Number>(Number::unbox(x) | Number::unbox(y))")
  (defn bit-xor [x y] "return obj<Number>(Number::unbox(x) ^ Number::unbox(y))")

  (defn bit-not [x] "return obj<Number>(~ Number::unbox(x))")

  (defn bit-shift-left [x n] "return obj<Number>(Number::unbox(x) << Number::unbox(n))")
  (defn bit-shift-right [x n] "return obj<Number>(Number::unbox(x) >> Number::unbox(n))")

  (defn identity [x] x)

  (defn map [f coll]
    (lazy-seq!
      (fn []
        (if (sequence? coll)
          (cons (f (first coll)) (map f (rest coll)))))))

  (defn range [n] "return _range(0, Number::unbox(n))")

  (defn take [n coll]
    (lazy-seq!
      (fn []
        (if (sequence? coll)
          (if (> n 0)
            (cons (first coll) (take (- n 1) (rest coll))))))))

  (defn take-while [pred? s]
    (lazy-seq!
      (fn []
        (if (sequence? s)
          (if (pred? (first s))
            (cons (first s) (take-while pred? (rest s))))))))

  (defn drop-while-aux [pred coll]
    "Var s = coll;

     while (_call(pred, s))
       s = _rest(s);

     return s")

  (defn drop-while [pred? coll]
    (lazy-seq!
      (fn []
        (drop-while-aux (fn [s] (if (sequence? s) (pred? (first s)) false)) coll))))

  (defn concat1 [x]
    (if (sequence? x)
      (cons (first x) (lazy-seq! (fn [] (concat1 (rest x)))))))

  (defn concat [x y]
    (if (sequence? x)
      (cons (first x) (lazy-seq! (fn [] (concat (rest x) y))))
      (concat1 y)))

  (defn filter [pred? coll]
    (lazy-seq!
      (fn []
        (if (sequence? coll)
          (let [[f & r] coll]
            (if (pred? f)
              (cons f (filter pred? r))
              (filter pred? r)))))))

  (defn partition [n coll]
    (lazy-seq!
      (fn []
        (if (sequence? coll)
          (let [p (take n coll)]
            (if (= n (count p))
              (cons p (partition n (nthrest coll n)))))))))

  (defn interleave [s1 s2]
    (lazy-seq!
      (fn []
        (if (sequence? s1)
          (if (sequence? s2)
            (cons (first s1) (cons (first s2) (interleave (rest s1) (rest s2)))))))))

  (defn flatten [s]
    (lazy-seq!
      (fn []
        (if (sequence? s)
          (if (sequence? (first s))
            (concat (flatten (first s)) (flatten (rest s)))
            (cons (first s) (flatten (rest s))))))))

  (defn string? [s] "return s.is_type(type_id<String>) ? cached::true_o : cached::false_o")

  (defn println [n]
    "std::cout << Number::unbox(n) << std::endl;

     return nil()")
))

(defn escape-string [s] (escape s (hash-map \" "\\\"", \\ "\\\\")))

(defn form?
  ([s] (fn [f] (form? s f)))
  ([s f] (and (seq? f) (= (first f) s))))

(defn ffi-fn? [body] (and (seq body) (every? string? body)))

(defn fn-arg-symbol? [s] (and (symbol? s) (not (= s '&)) (not (= s '_))))

(defn transform [tree pred? f] (prewalk (fn [form] (if (pred? form) (f form) form)) tree))

(defn let-closure [bindings body]
  (if (empty? bindings)
    (list (apply list 'fn [] body))
    (if (odd? (count bindings))
      (throw (Error. (str "let requires an even number of forms in binding vector => " bindings)))
      (letfn [(close- [[arg val] & more] (list (apply list 'fn [arg] (if (seq more) (list (apply close- more)) body)) val))]
        (apply close- (partition 2 bindings))))))

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
  (let [name ((deref fns) (apply list env args body))]
    (if name
      (apply list 'ast-fn name env))))

(defn define-fn [fns env args body]
  (let [name (gensym "Lambda__")]
    (swap! fns assoc (apply list env args body) name)
    (apply list 'ast-fn name env)))

(defn fn->lift [form]
   (letfn [(lift- [form fns env]
             (transform form (form? 'ast-lambda)
               (fn [[_ args & body]]
                 (let [body (lift- body fns (concat args env))
                       syms (reduce conj (hash-set) (filter symbol? (flatten body)))
                       env  (apply list (filter syms (reduce conj (hash-set) (flatten env))))
                       args (if (ffi-fn? body)
                              args
                              (transform args symbol? (fn [v] (if (or (not (fn-arg-symbol? v)) (syms v)) v '_))))]
                   (or (fn-defined? fns env args body) (define-fn fns env args body))))))]
     (let [fns (atom (ordered-map)), form (lift- form fns nil)]
       (concat (map (fn [[body name]] (apply list 'ast-defn name body)) (deref fns)) form))))

(defn compile [form] (fn->lift (expand-macros (concat ermine-runtime form))))

(defn c11-symbol [s]
  (if (= 'not s) '_not_
    (if (= '- s) '_minus_
      (symbol (escape (str s) (hash-map \- "_", \* "_star_", \+ "_plus_", \/ "_slash_", \< "_lt_", \> "_gt_", \= "_eq_", \? "_qmark_", \! "_bang_", \# "__"))))))

(defn c11-symbols [form] (transform form symbol? c11-symbol))

(declare c11-form)

(defn c11-form* [model form] (map (fn [f] (c11-form model f)) form))

(defn c11-model [form]
  (let [model (atom (hash-map :symbols (hash-set), :lambdas (list))), program (doall (c11-form* model (c11-symbols form)))]
    (swap! model update :lambdas reverse)
    (assoc (deref model) :program (remove empty? program))))

(defn c11-def [model [_ name & form]]
  (swap! model update :symbols conj name)
  (apply str name " = " (c11-form* model form)))

(defn c11-if [model [_ test then else]]
  (let [test (c11-form model test)
        then (c11-form model then)
        else (if (nil? else) "nil()" (c11-form model else))]
    (apply str "(" test " ? " then " : " else ")")))

(defn c11-list [model [_ & args]] (str "_list(" (apply str (interpose ", " (c11-form* model args))) ")"))

(defn c11-call [name args] (str "_call(" name (if (seq args) (apply str ", " (interpose ", " args)) "") ")"))

(defn c11-nth* [s i] (reduce (fn [s r] (str r "(" s ")")) s (repeat i "_rest")))
(defn c11-nth [s i] (str "_first(" (c11-nth* s i) ")"))

(defn c11-fn-arg [name s i] (str "Ref " name " = " (c11-nth s i)))
(defn c11-fn-arg* [name s i] (str "Ref " name " = " (c11-nth* s i)))

(declare destructure-args)

(defn destructure-seq [args parent]
  (map
    (fn [[i arg]]
      (if (symbol? arg)
        (c11-fn-arg arg parent i)
        (if (coll? arg)
          (destructure-args arg (c11-nth parent i)))))
    (remove (fn [%] (= (second %) '_)) (map list (range) args))))

(defn destructure-more [more parent i]
  (if (nil? more)
    (list)
    (if (symbol? more)
      (c11-fn-arg* more parent i)
      (if (coll? more)
        (let [tmp# (gensym)]
          (list (c11-fn-arg* tmp# parent i) (destructure-args more tmp#)))))))

(defn destructure-args [args parent]
  (let [arg? (fn [%] (not (= % '&)))
        more (second (drop-while arg? args))
        args (take-while arg? args)]
    (list (destructure-seq args parent) (destructure-more more parent (count args)))))

(defn c11-fn [model name env args body]
  (let [body (if (empty? body) (list "return nil()")
               (if (ffi-fn? body) (list (apply str body))
                 (let [[r & s] (reverse (c11-form* model body))]
                   (reverse (cons (str "return " r) s)))))
        env  (filter fn-arg-symbol? (flatten env))
        vars (flatten (destructure-args args "_args_"))]
    (hash-map :name name :env env :args args :vars vars :body body)))

(defn c11-defn [model [_ name env args & body]] (swap! model update :lambdas (fn [%] (cons (c11-fn model name env args body) %))) "")

(defn c11-form [m f]
  (if (form? 'ast_defn f) (c11-defn m f)
    (if (form? 'ast_fn f)   (let [[_ name & env] f] (str "obj<" name ">(" (apply str (interpose ", " (filter fn-arg-symbol? (flatten env)))) ")"))
      (if (form? 'list f)     (c11-list m f)
        (if (form? 'if f)       (c11-if m f)
          (if (form? 'def f)      (c11-def m f)
            (if (symbol? f)         (str f)
              (if (number? f)         (str "obj<Number>(" (int f) ")")
                (if (nil? f)            "nil()"
                  (if (string? f)         (str "obj<String>(\"" (escape-string f) "\", " (count f) ")")
                    (if (boolean? f)        (if f "cached::true_o" "cached::false_o")
                      (if (seq? f)            (let [[fun & args] f] (c11-call (c11-form m fun) (c11-form* m args)))
                                                (throw (Error. (str "unsupported form => " f)))))))))))))))

(defn c11-syntax [model]
  (str
"
#include <atomic>
#include <iostream>
#include <mutex>

namespace ermine {
  struct Locking {
    std::mutex& lock;

    Locking(const Locking&) = delete;
    Locking(std::mutex& m) : lock(m) { lock.lock(); };
    ~Locking() { lock.unlock(); }
  };

  namespace memory {
    static std::mutex lock;

    static void* allocate(size_t s) {
      Locking _(lock);
      return ::malloc(s);
    }

    template <typename T>
    static void* allocate() { return allocate(sizeof(T)); }

    static void free(void* p) {
      Locking _(lock);
      ::free(p);
    }
  }

  template <typename>
  void type_id() { }

  using type_id_t = void(*)();
  typedef type_id_t type_t;

  struct Var;
  typedef Var const & Ref;

  struct Sequence;

  struct Object {
    std::atomic<int> rc;

    Object() : rc(0) { }
    virtual ~Object() { };

    virtual type_t __type() const = 0;

    virtual bool __equals(Ref r) const;

    virtual Sequence* __sequence() { return nullptr; }

    void operator delete(void* p) { memory::free(p); }

    void rc_inc() { rc++; }
    bool rc_dec() { return (--rc == 0); }
  };

  struct Var {
    Object* obj;

    Var(Object* o = nullptr) : obj(o) { rc_inc(); }
    Var(Ref r) : obj(r.obj) { rc_inc(); }
    Var(Var&& o) : obj(o.detach()) { }

    ~Var() { rc_dec(); }

    Var& operator=(Var&& o) {
      if (this != &o) {
        rc_dec();
        obj = o.detach();
      }
      return *this;
    }

    Var& operator=(Ref r) {
      if (obj != r.obj) {
        rc_dec();
        obj = r.obj;
        rc_inc();
      }
      return *this;
    }

    bool equals(Ref) const;

    bool operator==(Ref r) const { return equals(r); }
    bool operator!=(Ref r) const { return !equals(r); }

    operator bool() const;

    template <typename T>
    T* cast() const { return static_cast<T*>((Object*)obj); }

    bool is_type(type_t type) const {
      if (obj)
        return (static_cast<Object*>(obj)->__type() == type);
      else
        return false;
    }

    bool is_nil() const { return (obj == nullptr); }

    Object* detach() {
      Object* _obj = obj;
      obj = nullptr;
      return _obj;
    }

    void rc_inc() {
      if (obj)
        obj->rc_inc();
    }

    void rc_dec() {
      if (obj && obj->rc_dec()) {
        delete obj;
        obj = nullptr;
      }
    }
  };

  bool Object::__equals(Ref r) const { return (this == r.obj); }

  template <>
  Sequence* Var::cast<Sequence>() const { return obj->__sequence(); }

  template <typename T, typename... A>
  Var obj(A... args) {
    void* storage = memory::allocate<T>();

    return Var(new(storage) T(args...));
  }

  Var nil() {
    return Var();
  }
}

namespace ermine {
  Var _list(Ref x);

  template <typename... A>
  Var _list(Ref x, A const & ... args);

  bool _is_sequence(Ref x);

  Var _cons(Ref x, Ref s);
  Var _first(Ref s);
  Var _rest(Ref s);

  Var _nth(Var s, int n);
  Var _nthrest(Var s, int n);

  size_t _count(Var s);

  Var _range(int low, int high);

  template <typename T, typename... A>
  Var _call(T const & fun, A const & ... args);

  template <typename T>
  Var _call(T const & fun);

  template <>
  Var _call(Ref);

  Var _apply(Ref fun, Ref args);
}

namespace ermine {
  struct Sequence {
    virtual Var __cons(Ref x) = 0;
    virtual Var __first() = 0;
    virtual Var __rest() = 0;

    static bool equals(Var lhs, Var rhs) {
      for ( ; ; lhs = _rest(lhs), rhs = _rest(rhs)) {
        Ref lf = _first(lhs);
        Ref rf = _first(rhs);

        if (lf.is_nil() && rf.is_nil())
          return true;

        if (lf != rf)
          return false;
      }
    }
  };

  struct Fn : Object {
    virtual type_t __type() const { return type_id<Fn>; }

    virtual Var __invoke(Ref args) const = 0;
  };

  struct Boolean : Object {
    const bool value;

    Boolean(bool b) : value(b) { }

    virtual type_t __type() const { return type_id<Boolean>; }

    virtual bool __equals(Ref r) const {
      return (value == r.cast<Boolean>()->value);
    }
  };

  namespace cached {
    const Var true_o = obj<::ermine::Boolean>(true);
    const Var false_o = obj<::ermine::Boolean>(false);
  }

  Var::operator bool() const {
    if (obj == nullptr)
      return false;
    else if (obj->__type() == (type_t)type_id<Boolean>)
      return cast<Boolean>()->value;
    else
      return true;
  }

  bool Var::equals(Ref r) const {
    if (obj == r.obj)
      return true;
    else if (is_nil() || r.is_nil())
      return false;
    else if (_is_sequence(*this) && _is_sequence(r))
      return Sequence::equals(*this, r);
    else if (obj->__type() != r.obj->__type())
      return false;
    else
      return obj->__equals(r);
  }

  struct Number : Object {
    const int value;

    Number(int n) : value(n) { }

    virtual type_t __type() const { return type_id<Number>; }

    virtual bool __equals(Ref r) const {
      return (value == Number::unbox(r));
    }

    static int unbox(Ref r) {
      return r.cast<Number>()->value;
    }
  };

  struct EmptyList : Object {
    virtual type_t __type() const { return type_id<EmptyList>; }
  };

  namespace cached {
    const Var empty_list_o = obj<::ermine::EmptyList>();
  }

  struct Cons : Object, Sequence {
    const Var next;
    const Var data;

    Cons(Ref d = nil(), Ref n = nil()) : next(n), data(d) { }

    virtual type_t __type() const { return type_id<Cons>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __cons(Ref x) { return obj<Cons>(x, Var(this)); }
    virtual Var __first() { return data; }
    virtual Var __rest() { return next; }
  };

  Var _list() {
    return cached::empty_list_o;
  }

  Var _list(Ref x) {
    return obj<Cons>(x, cached::empty_list_o);
  }

  template <typename... A>
  Var _list(Ref x, A const & ... args) {
    return obj<Cons>(x, _list(args...));
  }

  struct LazySeq : Object, Sequence {
    std::mutex lock;
    Var data;
    Var thunk;

    LazySeq(Ref t) : thunk(t) { }
    LazySeq(Ref d, Ref t) : data(d), thunk(t) { }

    virtual type_t __type() const { return type_id<LazySeq>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __cons(Ref x) {
      Locking _(lock);

      if (data.is_nil())
        return obj<LazySeq>(x, thunk);
      else
        return obj<Cons>(x, Var((Object*)this));
    }

    virtual Var __first() {
      Locking _(lock);

      if (data.is_nil())
        return _first(_call(thunk));
      else
        return data;
    }

    virtual Var __rest() {
      Locking _(lock);
      Var s = _call(thunk);

      if (data.is_nil())
        return _rest(s);
      else if (s.is_nil())
        return _list();
      else
        return s;
    }
  };

  struct Map : Fn, Sequence {
    Var data;

    Map() : data(_list(_list())) { }

    Map(Ref l) : data(l) { }

    virtual type_t __type() const { return type_id<Map>; }

    Var assoc(Ref k, Ref v) const {
      Ref m = dissoc_aux(k);
      Ref _keys = _first(m);
      Ref _values = _rest(m);

      return obj<Map>(_cons(_cons(k, _keys), _cons(v, _values)));
    }

    Var dissoc_aux(Ref k) const {
      Ref _keys = _first(data);
      Var _values = _rest(data);

      Var ks;
      Var vs;

      for (Var i = _first(_keys), z = _rest(_keys); !z.is_nil(); i = _first(z), z = _rest(z)) {
        if (i != k) {
          ks = _cons(i, ks);
          vs = _cons(_first(_values), vs);
          _values = _rest(_values);
        }
      }

      return _cons(ks, vs);
    }

    Var dissoc(Ref k) const {
      return obj<Map>(dissoc_aux(k));
    }

    Var val_at(Ref args) const {
      Ref key = _first(args);
      Ref not_found = _first(_rest(args));

      Ref _keys = _first(data);
      Var _values = _rest(data);

      for (Var i = _first(_keys), z = _rest(_keys); !z.is_nil(); i = _first(z), z = _rest(z)) {
        if (key == i)
          return _first(_values);

        _values = _rest(_values);
      }

      if (!not_found.is_nil())
        return not_found;
      else
        return nil();
    }

    virtual Var __invoke(Ref args) const {
      return val_at(args);
    }

    Var vals() const { return _rest(data); }
    Var keys() const { return _first(data); }

    virtual Sequence* __sequence() { return this; }

    virtual Var __cons(Ref v) {
      return _list(v, data);
    }

    virtual Var __first() {
      Ref _keys = _first(data);
      Ref _values = _rest(data);

      return _list(_first(_keys), _first(_values));
    }

    virtual Var __rest() {
      Ref _keys = _first(data);
      Ref _values = _rest(data);

      if (_rest(_keys).is_type(type_id<EmptyList>))
        return _list();
      else
        return obj<Map>(_cons(_rest(_keys), _rest(_values)));
    }
  };

  template <>
  Var obj<Map>(Var keys, Var vals) {
    void* storage = memory::allocate<Map>();

    return Var(new(storage) Map(_cons(keys, vals)));
  }

  struct String : Object, Sequence {
    Var data;

    String() : data(_list()) { }

    String(Ref s) : data(s) { }

    virtual type_t __type() const { return type_id<String>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __cons(Ref x) {
      return obj<String>(_cons(x, data));
    }

    virtual Var __first() {
      return _first(data);
    }

    virtual Var __rest() {
      Ref r = _rest(data);

      if (r.is_type(type_id<EmptyList>))
        return _list();
      else
        return obj<String>(r);
    }
  };

  struct Atom : Object {
    std::mutex lock;
    Var data;

    Atom(Ref d) : data(d) { }

    virtual type_t __type() const { return type_id<Atom>; }

    Var swap(Ref f, Ref args) {
      Locking _(lock);
      data = f.cast<Fn>()->__invoke(_cons(data, args));
      return data;
    }

    Var reset(Ref newval) {
      Locking _(lock);
      data = newval;
      return data;
    }

    Var deref() {
      Locking _(lock);
      return data;
    }
  };
}

namespace _main {
  using namespace ermine;

"
    (apply str (interpose "\n" (map (fn [%] (str "  Var " % ";")) (:symbols model))))
"
}

namespace ermine {
  bool _is_sequence(Ref x) {
    if (x.cast<Sequence>())
      return true;
    else
      return false;
  }

  Var _cons(Ref x, Ref s) {
    if (s.is_nil() || s.is_type(type_id<EmptyList>))
      return _list(x);
    else
      return s.cast<Sequence>()->__cons(x);
  }

  Var _first(Ref s) {
    if (s.is_nil() || s.is_type(type_id<EmptyList>))
      return nil();
    else
      return s.cast<Sequence>()->__first();
  }

  Var _rest(Ref s) {
    if (s.is_nil() || s.is_type(type_id<EmptyList>))
      return nil();
    else
      return s.cast<Sequence>()->__rest();
  }

  Var _nth(Var s, int n) {
    if (n < 0)
      return nil();

    for (int i = 0; i < n; i++)
      s = _rest(s);

    return _first(s);
  }

  Var _nthrest(Var s, int n) {
    for (int i = 0; i < n; i++)
      s = _rest(s);

    if (s.is_nil())
      return _list();
    else
      return s;
  }

  size_t _count(Var s) {
    size_t n = 0;

    for (s = _rest(s); !s.is_nil(); s = _rest(s))
      n++;

    return n;
  }

  Var _range(int low, int high) {
    struct Range : Fn {
      int low, high;

      Range(int l, int h) : low(l), high(h) { }

      virtual Var __invoke(Ref) const {
        if (low < high)
          return obj<LazySeq>(obj<Number>(low), obj<Range>((low + 1), high));
        else
          return nil();
      }
    };

    return obj<LazySeq>(obj<Range>(low, high));
  }

  template <typename T, typename... A>
  Var _call(T const & fun, A const & ... args) {
    return fun.__invoke(_list(args...));
  }

  template <typename T>
  Var _call(T const & fun) {
    return fun.__invoke(nil());
  }

  template <>
  Var _call(Ref fun) {
    return fun.cast<Fn>()->__invoke(nil());
  }

  template <typename... A>
  Var _call(Ref fun, A const & ... args) {
    return fun.cast<Fn>()->__invoke(_list(args...));
  }

  Var _apply(Ref f, Ref args) {
    if (_rest(args).is_type(type_id<EmptyList>))
      return f.cast<Fn>()->__invoke(_first(args));

    struct {
      Var operator()(Ref s) const {
        Ref x = _first(s);

        if (x.is_nil())
          return cached::empty_list_o;

        if (x.cast<Sequence>())
          return x;

        return _cons(x, (*this)(_rest(s)));
      }
    } spread;

    return f.cast<Fn>()->__invoke(spread(args));
  }
}

namespace _main {
"
    (apply str (map (fn [f] (str
"
  struct " (:name f) " : Fn {
"
      (if (seq (:env f)) (str
        (apply str (interpose "\n" (map (fn [%] (str "    const Var " % ";")) (:env f))))
"
    " (:name f) " (" (apply str (interpose ", " (map (fn [%] (str "Ref " %)) (:env f)))) ") : "
                     (apply str (interpose ", " (map (fn [%] (str % "(" % ")")) (:env f)))) " { }
"
      ))
"
    virtual Var __invoke(Ref _args_) const {
      (void)(_args_);
"
      (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (:vars f))))
      (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (:body f))))
"
    }
  };
"
      )) (:lambdas model)))
"

  int main() {
"
    (apply str (interpose "\n" (map (fn [%] (str "    " % ";")) (:program model))))
"
    return 0;
  }
}

int main() {
  return _main::main();
}
"))

(defn -main [& args]
    (print (c11-syntax (c11-model (compile (read-string (str "(" (apply str (interleave (take-while some? (repeatedly read-line)) (repeat "\n"))) ")")))))))
