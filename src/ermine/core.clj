(ns ermine.core
  (:refer-clojure :only #_[& -1 0 1 def fn* if nil quote] [+ < = apply assoc conj contains? deref first get hash-map hash-set int list next number? print read-line read-string seq seq? sequential? str string? swap! symbol symbol?  defmacro identical? vector  *ns* *print-length* .. intern])
  (:require [clojure.core :as -]))

(defmacro λ [args body] (list 'fn* args body))

(defmacro let [x y z] (list (list 'λ (vector x) z) y))

(def Ζ (λ [f] ((λ [x] (x x)) (λ [x] (f (λ [& s] (apply (x x) s)))))))

(defmacro ζ [! args body] (list 'fn* ! args body))

(def dec (λ [n] (+ n -1)))
(def inc (λ [n] (+ n 1)))

(def neg? (λ [n] (< n 0)))
(def pos? (λ [n] (< 0 n)))

(defmacro Atom. [x] (list 'new 'clojure.lang.Atom x))

(def atom (λ [x] (Atom. x)))

(let i' (atom 0)
  (def gensym (λ [prefix] (symbol (str prefix (swap! i' inc))))))

(defmacro and [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# y x#))))
(defmacro or [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# x# y))))

(def identity (λ [x] x))
(def constantly (λ [x] (λ [& _] x)))

(def nil? (λ [x] (identical? x nil)))
(def not (λ [x] (if x nil 'true)))
(def some? (λ [x] (not (nil? x))))

(def count (λ [s] ((ζ ! [n s] (if s (! (inc n) (next s)) n)) 0 (seq s))))
(def nth (λ [s n not-found] ((ζ ! [s n] (if (and s (pos? n)) (if (neg? n) (first s) (! (next s) (dec n))) not-found)) (seq s) n)))

(def second (λ [s] (first (next s))))
(def third (λ [s] (first (next (next s)))))

(def some (λ [f? s] (if (seq s) (or (f? (first s)) (some f? (next s))))))

(defmacro Cons. [car cdr] (list 'new 'clojure.lang.Cons car cdr))

(def cons (λ [x s] (if (nil? s) (list x) (if (seq? s) (Cons. x s) (Cons. x (seq s))))))

(defmacro LazySeq. [thunk] (list 'new 'clojure.lang.LazySeq thunk))
(defmacro lazy-seq [thunk] (list 'LazySeq. (list 'λ (vector) thunk)))

(def repeat (λ [x] (lazy-seq (cons x (repeat x)))))
(def repeatedly (λ [f] (lazy-seq (cons (f) (repeatedly f)))))

(def concat (λ [s1 s2] (lazy-seq (if (seq s1) (cons (first s1) (concat (next s1) s2)) s2))))
(def flatten (λ [x]
  (if (sequential? x) ((ζ ! [s] (lazy-seq (if (seq s) (let x (first s) (if (sequential? x) (concat (! x) (! (next s))) (cons x (! (next s)))))))) x) x)))

(def filter (λ [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (filter f? (next s))) (filter f? (next s))))))))

(def take-while (λ [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (take-while f? (next s)))))))))
(def drop-while (λ [f? s] (lazy-seq ((ζ ! [s] (if (and s (f? (first s))) (! (next s)) s)) (seq s)))))

(def take (λ [n s] (lazy-seq (if (and (pos? n) (seq s)) (cons (first s) (take (dec n) (next s)))))))
(def nthnext (λ [s n] ((ζ ! [s n] (if (and s (pos? n)) (! (next s) (dec n)) s)) (seq s) n)))

(def interleave (λ [s1 s2] (lazy-seq (if (and (seq s1) (seq s2)) (cons (first s1) (cons (first s2) (interleave (next s1) (next s2))))))))
(def interpose (λ [x s] (next (interleave (repeat x) s))))

(def map (λ [f s] (lazy-seq (if (seq s) (cons (f (first s)) (map f (next s)))))))
(def map-indexed (λ [f i s] (lazy-seq (if (seq s) (cons (f i (first s)) (map-indexed f (inc i) (next s)))))))

(def reduce (λ [f r s] ((ζ ! [r s] (if s (! (f r (first s)) (next s)) r)) r (seq s))))

(def reverse (λ [s] (reduce (λ [s x] (cons x s)) nil s)))

(def update (λ [m k f & s] (assoc m k (apply f (get m k nil) s))))

(def form? (λ [s] (λ [f] (and (seq? f) (= (first f) s)))))

(def fn-arg-symbol? (λ [s] (and (symbol? s) (not (= s '&)))))

(def transform (λ [form f? g]
  ((ζ ! [f form] ((λ [f form] (if (sequential? form) (apply list (map f form)) form)) (λ [form] (! f form)) (f form))) (λ [form] (if (f? form) (g form) form)) form)))
(def transform* (λ [form f? g*] (transform form f? (λ [s] (apply g* (next s))))))

(def compile (λ [form]
  (let fn-made-unique
        (λ [args body]
          (let syms (filter fn-arg-symbol? args)
            (let uniq (apply hash-map (interleave syms (map (λ [%] (symbol (str % (gensym "__")))) syms)))
              (let uniq (λ [%] (get uniq % nil))
                (list 'ast-lambda (transform args uniq uniq) (transform body uniq uniq))))))
    (let expand-macros
          (λ [s]
            (let s (transform s (form? 'ns)        (constantly 'nil))
              (let s (transform s (form? 'defmacro)  (constantly 'nil))
                (let s (transform* s (form? 'and)      (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# y x#)))))
                  (let s (transform* s (form? 'or)       (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# x# y)))))
                    (let s (transform* s (form? 'lazy-seq) (λ [thunk] (list 'LazySeq. (list 'λ (vector) thunk))))
                      (let s (transform* s (form? 'let)      (λ [x y z] (list (list 'λ (vector x) z) y)))
                        (let s (transform* s (form? 'ζ)        (λ [! args body] (list 'Ζ (list 'λ (vector !) (list 'λ args body)))))
                          (let s (transform* s (form? 'λ)        fn-made-unique)
                                   (transform* s (form? 'vector)   (λ [& v] (apply list 'list v))))))))))))
      (let fn->lift
            (λ [form]
              (let a'defs (atom nil)
                (let f'def
                      (λ [env args body]
                        (let name (some (λ [%] (if (= (next (next %)) (list env args body)) (second %))) (deref a'defs))
                          (if name
                            (apply list 'ast-fn name env))))
                  (let f'def!
                        (λ [env args body]
                          (let name (gensym "Fun__")
                            (let _ (swap! a'defs (λ [%] (cons (list 'ast-defn name env args body) %)))
                              (apply list 'ast-fn name env))))
                    (let f'lift
                          (ζ ! [form env]
                            (transform* form (form? 'ast-lambda)
                              (λ [args body]
                                (let body (! body (concat args env))
                                  (let syms (reduce conj (hash-set) (filter symbol? (flatten (list body))))
                                    (let env  (apply list (filter (λ [s] (contains? syms s)) (reduce conj (hash-set) env)))
                                      (let args (map (λ [s] (if (or (= s '&) (contains? syms s)) s '_)) args)
                                        (or (f'def env args body) (f'def! env args body)))))))))
                      (let form (f'lift form nil)
                        (concat (reverse (deref a'defs)) form)))))))
        (fn->lift (expand-macros form)))))))

(def escape (λ [s m] (apply str (map (λ [c] (get m c c)) (map str s)))))

(def c11-model (λ [form]
  (let f'escape
        (λ [s]
          (if (= 'not s) '_not_
            (if (= '- s) '_minus_
              (symbol (escape (str s)
                        (hash-map "-" "_", "*" "_star_", "+" "_plus_", "/" "_slash_", "<" "_lt_", ">" "_gt_", "=" "_eq_", "?" "_qmark_", "!" "_bang_", "'" "_apos_", "#" "__"))))))
    (let a'model (atom (hash-map 'symbols (hash-set), 'functions nil))
      (let f'emit
            (ζ ! [form]
              (let f'destructure
                    (λ [args]
                      (let e'nth* (λ [s i] (reduce (λ [s r] (str r "(" s ")")) s (take i (repeat "_next"))))
                        (let e'nth (λ [s i] (str "_first(" (e'nth* s i) ")"))
                          (let d'args (λ [args] (map-indexed (λ [i name] (str "Ref " name " = " (e'nth "_args_" i))) 0 args))
                            (let d'more (λ [name i] (if (some? name) (list (str "Ref " name " = " (e'nth* "_args_" i)))))
                              (let not-amp? (λ [s] (not (= s '&)))
                                (let more (second (drop-while not-amp? args))
                                  (let args (take-while not-amp? args)
                                    (concat (d'args args) (d'more more (count args)))))))))))
                (let f'defn
                      (λ [name env args body]
                        (list 'Fun name (filter fn-arg-symbol? env) (f'destructure args) (! body)))
                  (let f'list
                        (λ [f & s]
                          (if (= f 'ast_defn) (let _ (swap! a'model update 'functions (λ [%] (cons (apply f'defn s) %))) nil)
                            (if (= f 'ast_fn)   (str "obj<" (first s) ">(" (apply str (interpose ", " (filter fn-arg-symbol? (next s)))) ")")
                              (if (= f 'if)       (str "(" (! (first s)) " ? " (! (second s)) " : " (! (third s)) ")")
                                (if (= f 'Atom.)    (str "obj<Atom>(" (! (first s)) ")")
                                  (if (= f 'Cons.)    (str "obj<Cons>(" (! (first s)) ", " (! (second s)) ")")
                                    (if (= f 'LazySeq.) (str "obj<LazySeq>(" (! (first s)) ")")
                                      (if (= f 'def)      (let name (first s) (let _ (swap! a'model update 'symbols conj name)
                                                            (apply str name " = " (! (second s)))))
                                                          (let name (! f) (let args (map ! s)
                                                            (str "_call(" name (if (seq args) (apply str ", " (interpose ", " args))) ")")))))))))))
                    (if (symbol? form) (str form)
                      (if (number? form) (str "obj<Number>(" (int form) ")")
                        (if (string? form) (str "obj<String>(\"" (escape form (hash-map "\"" "\\\"", "\\" "\\\\")) "\", " (count form) ")")
                          (if (nil? form)    "nil()"
                            (if (seq? form)    (apply f'list form))))))))))
        (let program (apply list (map f'emit (transform form symbol? f'escape)))
          (let _ (swap! a'model update 'functions reverse)
            (assoc (deref a'model) 'program (filter seq program)))))))))

(def c11-syntax (λ [model]
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

  Var::operator bool() const {
    if (obj == nullptr)
      return false;
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

  struct Fun : Object {
    virtual type_t __type() const { return type_id<Fun>; }

    virtual Var __apply(Ref args) const = 0;
  };

  Var _list() { return nil(); }

  template <typename... A>
  Var _list(Ref x, A const & ... args) {
    return obj<Cons>(x, _list(args...));
  }

  Var _call(Ref fun) {
    return fun.cast<Fun>()->__apply(_list());
  }

  template <typename... A>
  Var _call(Ref fun, A const & ... args) {
    return fun.cast<Fun>()->__apply(_list(args...));
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

  struct Map : Fun, Sequence {
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

    virtual Var __apply(Ref args) const {
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
      data = f.cast<Fun>()->__apply(_cons(data, args));
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
    (apply str (interpose "\n" (map (λ [%] (str "  Var " % ";")) (get model 'symbols nil))))
    (apply str (map (λ [fun]
      (apply (λ [name env vars body]
        (str
"
  struct " name " : Fun {
"
      (if (seq env) (str
        (apply str (interpose "\n" (map (λ [%] (str "    const Var " % ";")) env)))
"
    " name " (" (apply str (interpose ", " (map (λ [%] (str "Ref " %)) env))) ") : "
                (apply str (interpose ", " (map (λ [%] (str % "(" % ")")) env))) " { }
"
      ))
"
    virtual Var __apply(Ref _args_) const {
      (void)(_args_);
"
      (apply str (interpose "\n" (map (λ [%] (str "      " % ";")) vars)))
"
      return " body ";
    }
  };
"
        )) (next fun))) (get model 'functions nil)))
"

  int main() {
"
    (apply str (interpose "\n" (map (λ [%] (str "    " % ";")) (get model 'program nil))))
"
    return 0;
  }
}

int main() {
  return _main::main();
}
")))

(def -main (λ [& _]
    (print (c11-syntax (c11-model (compile (read-string (str "(" (apply str (interleave (take-while some? (repeatedly read-line)) (repeat "\n"))) ")"))))))))
