(ns ermine.core
  (:refer-clojure :only #_[& -1 0 1 def fn* if nil quote] [+ < = apply assoc conj deref first get hash-map hash-set int list next number? print read-line read-string seq seq? sequential? str string? swap! symbol symbol?  defmacro identical? vector  *ns* *print-length* .. intern])
  (:require [clojure.core :as -]))

(defmacro λ [args & body] (apply list 'fn* args body))

(defmacro declare [name] (list 'def name))
(defmacro defn [name args & body] (list 'def name (apply list 'λ args body)))

(defn second [s] (first (next s)))
(defn third [s] (first (next (next s))))

(defmacro let [x y z] (list (list 'λ (vector x) z) y))

(defn Z [f] ((λ [x] (x x)) (λ [x] (f (λ [& s] (apply (x x) s))))))

(defn dec [n] (+ n -1))
(defn inc [n] (+ n 1))

(defn neg? [n] (< n 0))
(defn pos? [n] (< 0 n))

(defmacro Atom. [x] (list 'new 'clojure.lang.Atom x))

(defn atom [x] (Atom. x))

(let i' (atom 0)
  (defn gensym [prefix] (symbol (str prefix (swap! i' inc)))))

(defmacro and [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# y x#))))
(defmacro or [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# x# y))))

(defn identity [x] x)
(defn constantly [x] (λ [& _] x))

(defn nil? [x] (identical? x nil))
(defn not [x] (if x nil 'true))
(defn some? [x] (not (nil? x)))

(defn count [s] ((λ ! [n s] (if s (! (inc n) (next s)) n)) 0 (seq s)))
(defn nth [s n not-found] ((λ ! [s n] (if (and s (pos? n)) (if (neg? n) (first s) (! (next s) (dec n))) not-found)) (seq s) n))

(defn some [f? s] (if (seq s) (or (f? (first s)) (some f? (next s)))))

(defmacro Cons. [car cdr] (list 'new 'clojure.lang.Cons car cdr))

(defn cons [x s] (if (nil? s) (list x) (if (seq? s) (Cons. x s) (Cons. x (seq s)))))

(defmacro LazySeq. [thunk] (list 'new 'clojure.lang.LazySeq thunk))
(defmacro lazy-seq [thunk] (list 'LazySeq. (list 'λ (vector) thunk)))

(defn repeat [x] (lazy-seq (cons x (repeat x))))
(defn repeatedly [f] (lazy-seq (cons (f) (repeatedly f))))

(defn concat [s1 s2] (lazy-seq (if (seq s1) (cons (first s1) (concat (next s1) s2)) s2)))
(defn flatten [s] (lazy-seq (if (seq s) (let x (first s) (if (sequential? x) (concat (flatten x) (flatten (next s))) (cons x (flatten (next s))))))))

(defn filter [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (filter f? (next s))) (filter f? (next s)))))))

(defn take-while [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (take-while f? (next s))))))))
(defn drop-while [f? s] (lazy-seq ((λ ! [s] (if (and s (f? (first s))) (! (next s)) s)) (seq s))))

(defn take [n s] (lazy-seq (if (and (pos? n) (seq s)) (cons (first s) (take (dec n) (next s))))))
(defn nthnext [s n] ((λ ! [s n] (if (and s (pos? n)) (! (next s) (dec n)) s)) (seq s) n))

(defn interleave [s1 s2] (lazy-seq (if (and (seq s1) (seq s2)) (cons (first s1) (cons (first s2) (interleave (next s1) (next s2)))))))
(defn interpose [x s] (next (interleave (repeat x) s)))

(defn map [f s] (lazy-seq (if (seq s) (cons (f (first s)) (map f (next s))))))
(defn map-indexed [f i s] (lazy-seq (if (seq s) (cons (f i (first s)) (map-indexed f (inc i) (next s))))))

(defn reduce [f r s] ((λ ! [r s] (if s (! (f r (first s)) (next s)) r)) r (seq s)))

(defn reverse [s] (reduce (λ [s x] (cons x s)) (list) s))

(defn update [m k f & s] (assoc m k (apply f (get m k) s)))

(defn form? [s] (λ [f] (and (seq? f) (= (first f) s))))

(defn fn-arg-symbol? [s] (and (symbol? s) (not (= s '&))))

(defn transform [form f? g]
  ((λ ! [f form] ((λ [f form] (if (sequential? form) (apply list (map f form)) form)) (λ [form] (! f form)) (f form))) (λ [form] (if (f? form) (g form) form)) form))
(defn transform* [form f? g*] (transform form f? (λ [s] (apply g* (next s)))))

(defn fn-made-unique [args & body]
  (if (symbol? args)
    (list 'Z (list 'λ (vector args) (apply list 'λ body)))
    (let syms (filter fn-arg-symbol? args)
      (let uniq (apply hash-map (interleave syms (map (λ [%] (symbol (str % (gensym "__")))) syms)))
        (apply list 'ast-lambda (transform args uniq uniq) (transform body uniq uniq))))))

(defn expand-macros [s]
  (let s (transform s (form? 'ns)        (constantly 'nil))
    (let s (transform s (form? 'defmacro)  (constantly 'nil))
      (let s (transform* s (form? 'declare)  (λ [name] (list 'def name)))
        (let s (transform* s (form? 'defn)     (λ [name args & body] (list 'def name (apply list 'λ args body))))
          (let s (transform* s (form? 'and)      (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# y x#)))))
            (let s (transform* s (form? 'or)       (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# x# y)))))
              (let s (transform* s (form? 'lazy-seq) (λ [thunk] (list 'LazySeq. (list 'λ (vector) thunk))))
                (let s (transform* s (form? 'let)      (λ [x y z] (list (list 'λ (vector x) z) y)))
                  (let s (transform* s (form? 'λ)        fn-made-unique)
                           (transform* s (form? 'vector)   (λ [& v] (apply list 'list v)))))))))))))

(defn fn-defined? [a'defs env args body]
  (let name (some (λ [%] (if (= (next (next %)) (apply list env args body)) (second %))) (deref a'defs))
    (if name
      (apply list 'ast-fn name env))))

(defn define-fn [a'defs env args body]
  (let name (gensym "Lambda__")
    (let _ (swap! a'defs (λ [%] (cons (apply list 'ast-defn name env args body) %)))
      (apply list 'ast-fn name env))))

(defn fn->lift [form]
   (let f'lift
          (λ ! [form a'defs env]
            (transform* form (form? 'ast-lambda)
              (λ [args & body]
                (let body (! body a'defs (concat args env))
                  (let syms (reduce conj (hash-set) (filter symbol? (flatten body)))
                    (let env  (apply list (filter syms (reduce conj (hash-set) env)))
                      (let args (map (λ [s] (if (or (= s '&) (syms s)) s '_)) args)
                        (or (fn-defined? a'defs env args body) (define-fn a'defs env args body)))))))))
     (let a'defs (atom nil)
       (let form (f'lift form a'defs nil)
         (concat (reverse (deref a'defs)) form)))))

(defn compile [form] (fn->lift (expand-macros form)))

(defn escape [s m] (apply str (map (λ [c] (or (m c) c)) (map str s))))

(defn c11-symbol [s]
  (if (= 'not s) '_not_
    (if (= '- s) '_minus_
      (symbol (escape (str s)
                (hash-map "-" "_", "*" "_star_", "+" "_plus_", "/" "_slash_", "<" "_lt_", ">" "_gt_", "=" "_eq_", "?" "_qmark_", "!" "_bang_", "'" "_apos_", "#" "__"))))))

(defn c11-symbols [form] (transform form symbol? c11-symbol))

(declare c11-form)

(defn c11-form* [a'model form] (map (λ [f] (c11-form a'model f)) form))

(defn c11-model [form]
  (let a'model (atom (hash-map 'symbols (hash-set), 'lambdas (list)))
    (let program (apply list (c11-form* a'model (c11-symbols form)))
      (let _ (swap! a'model update 'lambdas reverse)
        (assoc (deref a'model) 'program (filter seq program))))))

(defn c11-nth* [s i] (reduce (λ [s r] (str r "(" s ")")) s (take i (repeat "_next"))))
(defn c11-nth [s i] (str "_first(" (c11-nth* s i) ")"))

(defn destructure-args [args] (map-indexed (λ [i name] (str "Ref " name " = " (c11-nth "_args_" i))) 0 args))
(defn destructure-more [name i] (if (some? name) (list (str "Ref " name " = " (c11-nth* "_args_" i)))))

(defn c11-destructure [args]
  (let arg? (λ [%] (not (= % '&)))
    (let more (second (drop-while arg? args))
      (let args (take-while arg? args)
        (concat (destructure-args args) (destructure-more more (count args)))))))

(defn c11-return [a'model & body]
  (if (seq body)
    (let e (reverse (c11-form* a'model body)) (reverse (cons (str "return " (first e)) (next e))))
    (list "return nil()")))

(defn c11-defn [a'model name env args & body]
  (hash-map 'name name 'env (filter fn-arg-symbol? env) 'args args 'vars (c11-destructure args) 'body (apply c11-return a'model body)))

(defn c11-call [name args] (str "_call(" name (if (seq args) (apply str ", " (interpose ", " args)) "") ")"))

(defn c11-list [a'model f & s]
  (if (= f 'ast_defn) (let _ (swap! a'model update 'lambdas (λ [%] (cons (apply c11-defn a'model s) %))) "")
    (if (= f 'ast_fn)   (str "obj<" (first s) ">(" (apply str (interpose ", " (filter fn-arg-symbol? (next s)))) ")")
      (if (= f 'if)       (str "(" (c11-form a'model (first s)) " ? " (c11-form a'model (second s)) " : " (c11-form a'model (third s)) ")")
        (if (= f 'Atom.)    (str "obj<Atom>(" (c11-form a'model (first s)) ")")
          (if (= f 'Cons.)    (str "obj<Cons>(" (c11-form a'model (first s)) ", " (c11-form a'model (second s)) ")")
            (if (= f 'LazySeq.) (str "obj<LazySeq>(" (c11-form a'model (first s)) ")")
              (if (= f 'def)      (let name (first s) (let _ (swap! a'model update 'symbols conj name) (apply str name " = " (c11-form* a'model (next s)))))
                                    (c11-call (c11-form a'model f) (c11-form* a'model s))))))))))

(defn c11-form [a'model f]
  (if (symbol? f)     (str f)
    (if (number? f)     (str "obj<Number>(" (int f) ")")
      (if (string? f)     (str "obj<String>(\"" (escape f (hash-map "\"" "\\\"", "\\" "\\\\")) "\", " (count f) ")")
        (if (nil? f)        "nil()"
          (if (seq? f)        (apply c11-list a'model f)))))))

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

  struct Fn : Object {
    virtual type_t __type() const { return type_id<Fn>; }

    virtual Var __apply(Ref args) const = 0;
  };

  Var _list() { return nil(); }

  template <typename... A>
  Var _list(Ref x, A const & ... args) {
    return obj<Cons>(x, _list(args...));
  }

  Var _call(Ref fun) {
    return fun.cast<Fn>()->__apply(_list());
  }

  template <typename... A>
  Var _call(Ref fun, A const & ... args) {
    return fun.cast<Fn>()->__apply(_list(args...));
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
      data = f.cast<Fn>()->__apply(_cons(data, args));
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
    (apply str (interpose "\n" (map (λ [%] (str "  Var " % ";")) ('symbols model))))
    (apply str (map (λ [f] (str
"
  struct " ('name f) " : Fn {
"
      (if (seq ('env f)) (str
        (apply str (interpose "\n" (map (λ [%] (str "    const Var " % ";")) ('env f))))
"
    " ('name f) " (" (apply str (interpose ", " (map (λ [%] (str "Ref " %)) ('env f)))) ") : "
                      (apply str (interpose ", " (map (λ [%] (str % "(" % ")")) ('env f)))) " { }
"
      ))
"
    virtual Var __apply(Ref _args_) const {
      (void)(_args_);
"
      (apply str (interpose "\n" (map (λ [%] (str "    " % ";")) ('vars f))))
      (apply str (interpose "\n" (map (λ [%] (str "    " % ";")) ('body f))))
"
    }
  };
"
      )) ('lambdas model)))
"

  int main() {
"
    (apply str (interpose "\n" (map (λ [%] (str "    " % ";")) ('program model))))
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
