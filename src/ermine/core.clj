(ns ermine.core
  (:refer-clojure :only #_[& -1 0 1 def fn* if nil] [= apply list print read-line read-string str symbol symbol?  defmacro  *ns* *print-length* .. intern])
  (:require [clojure.core :as -]))

(defmacro λ [args body] (list 'fn* (-/vec args) body))
(defmacro ζ [! args body] (list 'fn* ! (-/vec args) body))

(defmacro let [x y z] (list (list 'λ (list x) z) y))

(defmacro and [x y] (let x# (-/gensym "x__") (list 'let x# x (list 'if x# y x#))))
(defmacro or [x y] (let x# (-/gensym "x__") (list 'let x# x (list 'if x# x# y))))

(defmacro Atom. [x] (list 'new 'clojure.lang.Atom x))

(defmacro deref [a] (list '-/deref a))
(defmacro swap! [a f] (list '-/swap! a f))

(defmacro Cons. [car cdr] (list 'new 'clojure.lang.Cons car cdr))
(defmacro LazySeq. [thunk] (list 'new 'clojure.lang.LazySeq thunk))

(defmacro lazy-seq [thunk] (list 'LazySeq. (list 'λ nil thunk)))

(defmacro + [x y] (list '-/+ x y))
(defmacro < [x y] (list '-/< x y))

(defmacro nil? [x] (list '-/nil? x))

(defmacro number? [x] (list '-/number? x))
(defmacro string? [x] (list '-/string? x))

(defmacro seq? [x] (list '-/seq? x))

(defmacro first [s] (list '-/first s))
(defmacro next [s] (list '-/next s))

(defmacro do* [& s]
  (if s
    (apply (ζ ! [x & s]
      (if s
        (let f (first s)
          (apply ! (if (seq? f) (-/concat f (list x)) (list f x)) (next s)))
        x)) (-/reverse s))))

(def -main
  (do*
    (let Ζ (λ [f] ((λ [x] (x x)) (λ [x] (f (λ [& s] (apply (x x) s)))))))

    (let dec (λ [n] (+ n -1)))
    (let inc (λ [n] (+ n 1)))

    (let neg? (λ [n] (< n 0)))
    (let pos? (λ [n] (< 0 n)))

    (let atom (λ [x] (Atom. x)))

    (let gensym
      (let i' (atom 0)
        (λ [prefix]
          (symbol (str prefix (swap! i' inc))))))

    (let identity (λ [x] x))
    (let constantly (λ [x] (λ [& _] x)))

    (let not (λ [x] (if x nil -1)))
    (let some? (λ [x] (not (nil? x))))

    (let seq (λ [s] (if (seq? s) s nil)))

    (let count (λ [s] ((ζ ! [n s] (if s (! (inc n) (next s)) n)) 0 (seq s))))
    (let nth (λ [s n not-found] ((ζ ! [s n] (if (and s (pos? n)) (if (neg? n) (first s) (! (next s) (dec n))) not-found)) (seq s) n)))

    (let second (λ [s] (first (next s))))
    (let third (λ [s] (first (next (next s)))))

    (let some (ζ ! [f? s] (if (seq s) (or (f? (first s)) (! f? (next s))))))

    (let reduce (λ [f r s] ((ζ ! [r s] (if s (! (f r (first s)) (next s)) r)) r (seq s))))

    (let cons (λ [x s] (if (nil? s) (list x) (if (seq? s) (Cons. x s) (Cons. x (seq s))))))
    (let reverse (λ [s] (reduce (λ [s x] (cons x s)) nil s)))

    (let repeat (ζ ! [x] (lazy-seq (cons x (! x)))))
    (let repeatedly (ζ ! [f] (lazy-seq (cons (f) (! f)))))

    (let concat (ζ ! [s1 s2] (lazy-seq (if (seq s1) (cons (first s1) (! (next s1) s2)) s2))))
    (let flatten (λ [x] (if (seq? x) ((ζ ! [s] (lazy-seq (if (seq s) (let x (first s) (if (seq? x) (concat (! x) (! (next s))) (cons x (! (next s)))))))) x) x)))

    (let filter (ζ ! [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (! f? (next s))) (! f? (next s))))))))

    (let take-while (ζ ! [f? s] (lazy-seq (if (seq s) (let x (first s) (if (f? x) (cons x (! f? (next s)))))))))
    (let drop-while (λ [f? s] (lazy-seq ((ζ ! [s] (if (and s (f? (first s))) (! (next s)) s)) (seq s)))))

    (let take (ζ ! [n s] (lazy-seq (if (and (pos? n) (seq s)) (cons (first s) (! (dec n) (next s)))))))
    (let nthnext (λ [s n] ((ζ ! [s n] (if (and s (pos? n)) (! (next s) (dec n)) s)) (seq s) n)))

    (let interleave (ζ ! [s1 s2] (lazy-seq (if (and (seq s1) (seq s2)) (cons (first s1) (cons (first s2) (! (next s1) (next s2))))))))
    (let interpose (λ [x s] (next (interleave (repeat x) s))))

    (let partition (ζ ! [n s] (lazy-seq (if (seq s) (let p (take n s) (if (= (count p) n) (cons p (! n (nthnext s n)))))))))

    (let kv-map (ζ ! [& s] (if s (cons (list (first s) (second s)) (apply ! (next (next s)))))))
    (let kv-get (λ [m k] (some (λ [p] (if (= (first p) k) (second p))) m)))

    (let map (ζ ! [f s] (lazy-seq (if (seq s) (cons (f (first s)) (! f (next s)))))))
    (let map-indexed (ζ ! [f i s] (lazy-seq (if (seq s) (cons (f i (first s)) (! f (inc i) (next s)))))))

    (let form? (λ [s] (λ [f] (and (seq? f) (= (first f) s)))))

    (let fn-arg-symbol? (λ [s] (and (symbol? s) (not (= s '&)))))

    (let transform (λ [form f? g]
      ((ζ ! [f form] ((λ [f form] (if (seq? form) (apply list (map f form)) form)) (λ [form] (! f form)) (f form))) (λ [form] (if (f? form) (g form) form)) form)))
    (let transform* (λ [form f? g*] (transform form f? (λ [s] (apply g* (next s))))))

    (let compile
      (do*
        (let do*-macro
              (λ [& s]
                (if s
                  (apply (ζ ! [x & s]
                    (if s
                      (let f (first s)
                        (apply ! (if (seq? f) (concat f (list x)) (list f x)) (next s)))
                      x)) (reverse s)))))
        (let fn-made-unique
              (λ [args body]
                (let syms (filter fn-arg-symbol? args)
                  (let uniq (apply kv-map (interleave syms (map (λ [%] (symbol (str % (gensym "__")))) syms)))
                    (let uniq (λ [%] (kv-get uniq %))
                      (list 'ast-lambda (transform args uniq uniq) (transform body uniq uniq)))))))
        (let expand-macros
              (λ [s]
                (let s (transform s (form? 'ns)        (constantly 'nil))
                  (let s (transform s (form? 'defmacro)  (constantly 'nil))
                    (let s (transform* s (form? 'do*)      do*-macro)
                      (let s (transform* s (form? 'and)      (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# y x#)))))
                        (let s (transform* s (form? 'or)       (λ [x y] (let x# (gensym "x__") (list 'let x# x (list 'if x# x# y)))))
                          (let s (transform* s (form? 'lazy-seq) (λ [thunk] (list 'LazySeq. (list 'λ nil thunk))))
                            (let s (transform* s (form? 'let)      (λ [x y z] (list (list 'λ (list x) z) y)))
                              (let s (transform* s (form? 'ζ)        (λ [! args body] (list 'Ζ (list 'λ (list !) (list 'λ args body)))))
                                       (transform* s (form? 'λ)        fn-made-unique)))))))))))
        (let fn->lift
              (do*
                (let a'defs (atom nil))
                (let f'def
                      (λ [env args body]
                        (let name (some (λ [%] (if (= (next (next %)) (list env args body)) (second %))) (deref a'defs))
                          (if name
                            (apply list 'ast-fn name env)))))
                (let f'def!
                      (λ [env args body]
                        (let name (gensym "Fun__")
                          (let _ (swap! a'defs (λ [%] (cons (list 'ast-defn name env args body) %)))
                            (apply list 'ast-fn name env)))))
                (let s'contains?
                      (λ [s x]
                        (some (λ [%] (= % x)) s)))
                (let f'lift
                      (ζ ! [form env]
                        (transform* form (form? 'ast-lambda)
                          (λ [args body]
                            (let body (! body (concat args env))
                              (let set identity
                                (let syms (set (filter symbol? (flatten (list body))))
                                  (let env  (set (filter (λ [s] (s'contains? syms s)) env))
                                    (let args (map (λ [s] (if (or (= s '&) (s'contains? syms s)) s '_)) args)
                                      (or (f'def env args body) (f'def! env args body)))))))))))
                (λ [form]
                  (let form (f'lift form nil)
                    (concat (reverse (deref a'defs)) form)))))
        (λ [form]
          (fn->lift (expand-macros form)))))

    (let escape (λ [s m] (apply str (map (λ [c] (or (kv-get m c) c)) (map str s)))))

    (let c11-model
      (do*
        (let m'escape
              (kv-map "-" "_", "%" "_5_", "." "_0_", "*" "_8_", "+" "_plus_", "/" "_7_", "<" "_lt_", ">" "_gt_", "=" "_eq_", "?" "_9_", "!" "_4_", "'" "_1_", "#" "_3_"))
        (let f'escape
              (λ [s]
                (if (= 'not s) '_not_
                  (if (= '- s) '_minus_
                    (symbol (escape (str s) m'escape))))))
        (let a'lambdas (atom nil))
        (let f'emit
              (ζ ! [form]
                (do*
                  (let f'destructure
                        (do*
                          (let e'nth* (λ [s i] (reduce (λ [s r] (str r "(" s ")")) s (take i (repeat "_next")))))
                          (let e'nth (λ [s i] (str "_first(" (e'nth* s i) ")")))
                          (let d'args (λ [args] (map-indexed (λ [i name] (str "Ref " name " = " (e'nth "_args_" i))) 0 args)))
                          (let d'more (λ [name i] (if (some? name) (list (str "Ref " name " = " (e'nth* "_args_" i))))))
                          (λ [args]
                            (let not-amp? (λ [s] (not (= s '&)))
                              (let more (second (drop-while not-amp? args))
                                (let args (take-while not-amp? args)
                                  (concat (d'args args) (d'more more (count args)))))))))
                  (let f'defn
                        (λ [name env args body]
                          (list 'Fun name (filter fn-arg-symbol? env) (f'destructure args) (! body))))
                  (let f'list
                        (λ [f & s]
                          (if (= f 'ast_defn)   (let _ (swap! a'lambdas (λ [%] (cons (apply f'defn s) %))) nil)
                            (if (= f 'ast_fn)     (str "obj<" (first s) ">(" (apply str (interpose ", " (filter fn-arg-symbol? (next s)))) ")")
                              (if (= f 'if)         (str "(" (! (first s)) " ? " (! (second s)) " : " (! (third s)) ")")
                                (if (= f '_plus_)     (str "obj<Number>(Number::unbox(" (! (first s)) ") + Number::unbox(" (! (second s)) "))")
                                  (if (= f '_lt_)       (str "(Number::unbox(" (! (first s)) ") < Number::unbox(" (! (second s)) ") ? _true : _false)")
                                    (if (= f 'Atom_0_)    (str "obj<Atom>(" (! (first s)) ")")
                                      (if (= f 'deref)      (str "_deref(" (! (first s)) ")")
                                        (if (= f 'swap_4_)    (str "_swap(" (! (first s)) ", " (! (second s)) ")")
                                          (if (= f 'Cons_0_)    (str "obj<Cons>(" (! (first s)) ", " (! (second s)) ")")
                                            (if (= f 'LazySeq_0_) (str "obj<LazySeq>(" (! (first s)) ")")
                                              (if (= f 'seq_9_)     (str "(" (! (first s)) ".cast<Sequence>() ? _true : _false)")
                                                (if (= f 'first)      (str "_first(" (! (first s)) ")")
                                                  (if (= f 'next)       (str "_next(" (! (first s)) ")")
                                                    (if (= f 'nil_9_)     (str "(" (! (first s)) ".is_nil() ? _true : _false)")
                                                      (if (= f 'number_9_)  (str "(" (! (first s)) ".cast<Number>() ? _true : _false)")
                                                        (if (= f 'string_9_)  (str "(" (! (first s)) ".cast<String>() ? _true : _false)")
                                                                                (let name (! f) (let args (map ! s)
                                                                                  (str "_call(" name (if (seq args) (apply str ", " (interpose ", " args))) ")")))
                                                        ))))))))))))))))))
                  (if (symbol? form) (str form)
                    (if (number? form) (str "obj<Number>(" form ")")
                      (if (string? form) (str "obj<String>(\"" (escape form (kv-map "\"" "\\\"", "\\" "\\\\")) "\", " (count form) ")")
                        (if (nil? form)    "nil()"
                          (if (seq? form)    (apply f'list form)))))))))
        (λ [form]
          (let program (apply list (map f'emit (transform form symbol? f'escape)))
            (cons (filter seq program) (reverse (deref a'lambdas)))))))

    (let c11-syntax (λ [program & lambdas]
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
    std::mutex lock;

    void* allocate(size_t s) {
      Locking _(lock);
      return std::malloc(s);
    }

    template <typename T>
    void* allocate() { return allocate(sizeof(T)); }

    void free(void* p) {
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

  template <typename T, typename... A>
  Var obj(A... args) {
    void* storage = memory::allocate<T>();

    return Var(new(storage) T(args...));
  }

  Var nil() {
    return Var();
  }

  struct Sequence {
    virtual Var __first() = 0;
    virtual Var __next() = 0;
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

  bool Sequence::equals(Var lhs, Var rhs) {
    for ( ; ; lhs = _next(lhs), rhs = _next(rhs)) {
      Ref lf = _first(lhs);
      Ref rf = _first(rhs);

      if (lf.is_nil() && rf.is_nil())
        return true;

      if (!lf.equals(rf))
        return false;
    }
  }

  struct Cons : Object, Sequence {
    const Var car;
    const Var cdr;

    Cons(Ref car, Ref cdr) : car(car), cdr(cdr) { }

    virtual type_t __type() const { return type_id<Cons>; }

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
  };

  int Number::unbox(Ref r) {
    return r.cast<Number>()->value;
  }

  const Var _true = obj<Number>(-1);
  const Var _false = nil();

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

  struct String : Object, Sequence {
    Var data;

    String() : data(nil()) { }

    String(Ref s) : data(s) { }

    virtual type_t __type() const { return type_id<String>; }

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

  Var _deref(Ref a) {
    return a.cast<Atom>()->deref();
  }

  Var _swap(Ref a, Ref f) {
    return a.cast<Atom>()->swap(f, nil());
  }
}

namespace _main {
  using namespace ermine;

"
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
        )) (next fun))) lambdas))
"

  int main() {
"
    (apply str (interpose "\n" (map (λ [%] (str "    " % ";")) program)))
"
    return 0;
  }
}

int main() {
  return _main::main();
}
"
      )))

    (λ [& _]
      (print (apply c11-syntax (c11-model (compile (read-string (str "(" (apply str (interleave (take-while some? (repeatedly read-line)) (repeat "\n"))) ")")))))))))
