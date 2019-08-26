(ns ermine.core
  (:refer-clojure :only [= and apply assoc atom boolean? coll? concat conj cons count declare defn deref doall drop-while empty? every? filter first flatten fn gensym hash-map hash-set int interleave interpose let letfn list map nil? not number? odd? or partition print range read-line read-string reduce remove repeat repeatedly reverse second seq seq? some? str string? swap! symbol symbol? take-while update  *ns* *print-length* .. intern]) (:require [clojure.core :as -])
  (:require [clojure.string :refer [escape]]
            [clojure.walk :refer [prewalk]]
            [flatland.ordered.map :refer [ordered-map]]))

(def ermine-runtime '(
  (defn println [n]
    "std::cout << Number::unbox(n) << std::endl;

     return nil()")
))

(defn escape-string [s] (escape s (hash-map \" "\\\"", \\ "\\\\")))

(defn form? [s] (fn [f] (and (seq? f) (= (first f) s))))

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

(defn c11-nth* [s i] (reduce (fn [s r] (str r "(" s ")")) s (repeat i "_next")))
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

(defn c11-if [model [test then else]]
  (let [test (c11-form model test)
        then (c11-form model then)
        else (if (nil? else) "nil()" (c11-form model else))]
    (str "(" test " ? " then " : " else ")")))

(defn c11-call [name args] (str "_call(" name (if (seq args) (apply str ", " (interpose ", " args)) "") ")"))

(defn c11-list [m [f & s]]
  (if (= f 'ast_defn) (let [[name env args & body] s] (swap! m update :lambdas (fn [%] (cons (c11-fn m name env args body) %))) "")
    (if (= f 'ast_fn)   (let [[name & env] s] (str "obj<" name ">(" (apply str (interpose ", " (filter fn-arg-symbol? (flatten env)))) ")"))
      (if (= f 'if)       (c11-if m s)
        (if (= f 'cons)     (let [[car cdr] s] (str "obj<Cons>(" (c11-form m car) ", " (c11-form m cdr) ")"))
          (if (= f 'def)      (let [[name & form] s] (swap! m update :symbols conj name) (apply str name " = " (c11-form* m form)))
                                (c11-call (c11-form m f) (c11-form* m s))))))))

(defn c11-form [m f]
  (if (symbol? f)     (str f)
    (if (number? f)     (str "obj<Number>(" (int f) ")")
      (if (nil? f)        "nil()"
        (if (string? f)     (str "obj<String>(\"" (escape-string f) "\", " (count f) ")")
          (if (boolean? f)    (if f "true_o" "false_o")
            (if (seq? f)        (c11-list m f)
                                  (throw (Error. (str "unsupported form => " f))))))))))

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
      return std::malloc(s);
    }

    template <typename T>
    static void* allocate() { return allocate(sizeof(T)); }

    static void free(void* p) {
      Locking _(lock);
      std::free(p);
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

    operator bool() const;

    template <typename T>
    T* cast() const { return static_cast<T*>((Object*)obj); }

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

  Var _first(Ref s);
  Var _next(Ref s);

  struct Sequence {
    virtual Var __first() = 0;
    virtual Var __next() = 0;

    static bool equals(Var lhs, Var rhs) {
      for ( ; ; lhs = _next(lhs), rhs = _next(rhs)) {
        Ref lf = _first(lhs);
        Ref rf = _first(rhs);

        if (lf.is_nil() && rf.is_nil())
          return true;

        if (!lf.equals(rf))
          return false;
      }
    }
  };

  Var _first(Ref s) {
    if (s.is_nil())
      return nil();
    else
      return s.cast<Sequence>()->__first();
  }

  Var _next(Ref s) {
    if (s.is_nil())
      return nil();
    else
      return s.cast<Sequence>()->__next();
  }

  struct Cons : Object, Sequence {
    const Var car;
    const Var cdr;

    Cons(Ref car, Ref cdr) : car(car), cdr(cdr) { }

    virtual type_t __type() const { return type_id<Cons>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __first() { return car; }
    virtual Var __next() { return cdr; }
  };

  Var _cons(Ref x, Ref s) {
    if (s.is_nil())
      return obj<Cons>(x, nil());
    else
      return obj<Cons>(x, Var((Object*)s.cast<Sequence>()));
  }

  struct Boolean : Object {
    const bool value;

    Boolean(bool b) : value(b) { }

    virtual type_t __type() const { return type_id<Boolean>; }

    virtual bool __equals(Ref r) const {
      return (value == r.cast<Boolean>()->value);
    }
  };

  const Var true_o = obj<Boolean>(true);
  const Var false_o = obj<Boolean>(false);

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
    else if ((*this).cast<Sequence>() && r.cast<Sequence>())
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

  struct Fn : Object {
    virtual type_t __type() const { return type_id<Fn>; }

    virtual Var __invoke(Ref args) const = 0;
  };

  Var _list() { return nil(); }

  template <typename... A>
  Var _list(Ref x, A const & ... args) {
    return obj<Cons>(x, _list(args...));
  }

  Var _call(Ref fun) {
    return fun.cast<Fn>()->__invoke(_list());
  }

  template <typename... A>
  Var _call(Ref fun, A const & ... args) {
    return fun.cast<Fn>()->__invoke(_list(args...));
  }

  struct LazySeq : Object, Sequence {
    std::mutex lock;
    Var data;
    Var thunk;

    LazySeq(Ref t) : thunk(t) { }
    LazySeq(Ref d, Ref t) : data(d), thunk(t) { }

    virtual type_t __type() const { return type_id<LazySeq>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __first() {
      Locking _(lock);

      if (data.is_nil())
        return _first(_call(thunk));
      else
        return data;
    }

    virtual Var __next() {
      Locking _(lock);
      Var s = _call(thunk);

      if (data.is_nil())
        return _next(s);
      else
        return s;
    }
  };

  struct Map : Fn, Sequence {
    Var data;

    Map() : data(obj<Cons>(nil(), nil())) { }

    Map(Ref l) : data(l) { }

    virtual type_t __type() const { return type_id<Map>; }

    Var assoc(Ref k, Ref v) const {
      Ref m = dissoc_aux(k);
      Ref _keys = _first(m);
      Ref _values = _next(m);

      return obj<Map>(_cons(_cons(k, _keys), _cons(v, _values)));
    }

    Var dissoc_aux(Ref k) const {
      Ref _keys = _first(data);
      Var _values = _next(data);

      Var ks;
      Var vs;

      for (Var i = _first(_keys), z = _next(_keys); !z.is_nil(); i = _first(z), z = _next(z)) {
        if (!i.equals(k)) {
          ks = _cons(i, ks);
          vs = _cons(_first(_values), vs);
          _values = _next(_values);
        }
      }

      return _cons(ks, vs);
    }

    Var dissoc(Ref k) const {
      return obj<Map>(dissoc_aux(k));
    }

    Var get(Ref key, Ref not_found) const {
      Ref _keys = _first(data);
      Var _values = _next(data);

      for (Var i = _first(_keys), z = _next(_keys); !z.is_nil(); i = _first(z), z = _next(z)) {
        if (key.equals(i))
          return _first(_values);

        _values = _next(_values);
      }

      if (!not_found.is_nil())
        return not_found;
      else
        return nil();
    }

    virtual Var __invoke(Ref args) const {
      Ref key = _first(args);
      Ref not_found = _first(_next(args));

      return get(key, not_found);
    }

    Var vals() const { return _next(data); }
    Var keys() const { return _first(data); }

    virtual Sequence* __sequence() { return this; }

    virtual Var __first() {
      Ref _keys = _first(data);
      Ref _values = _next(data);

      return obj<Cons>(_first(_keys), obj<Cons>(_first(_values), nil()));
    }

    virtual Var __next() {
      Ref _keys = _first(data);
      Ref _values = _next(data);

      if (_next(_keys).is_nil())
        return nil();
      else
        return obj<Map>(_cons(_next(_keys), _next(_values)));
    }
  };

  struct String : Object, Sequence {
    Var data;

    String() : data(nil()) { }

    String(Ref s) : data(s) { }

    virtual type_t __type() const { return type_id<String>; }

    virtual Sequence* __sequence() { return this; }

    virtual Var __first() {
      return _first(data);
    }

    virtual Var __next() {
      Ref r = _next(data);

      if (r.is_nil())
        return nil();
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
