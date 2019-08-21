(defobject "
struct seekable_i {
  virtual var cons(ref x) = 0;
  virtual var first() = 0;
  virtual var rest() = 0;

  static bool equals(var lhs, var rhs) {
    for ( ; ; lhs = rt::rest(lhs), rhs = rt::rest(rhs)) {
      ref lf = rt::first(lhs);
      ref rf = rt::first(rhs);

      if (lf.is_nil() && rf.is_nil())
        return true;

      if (lf != rf)
        return false;
    }
  }
};
")

(defobject "
struct lambda_i : object {
  type_t type() const { return type_id<lambda_i>; }

  virtual var invoke(ref args) const = 0;
};
")

(defobject "
struct deref_i : object {
  virtual var deref() = 0;
};
")

(defn deref [a] "return a.cast<deref_i>()->deref();")

(defobject "
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
  else if (rt::is_seqable(*this) && rt::is_seqable(o))
    return seekable_i::equals(*this, o);
  else if (obj->type() != o.get()->type())
    return false;
  else
    return get()->equals(o);
}
")

(defobject "
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
")

(defobject "
struct number final : object {
  type_t type() const final { return type_id<number>; }

  const real_t n;

  template <typename T> explicit number(T x) : n(real_t(x)) { }

  bool equals(ref o) const final {
    return (rt::abs(n - number::to<real_t>(o)) < real_epsilon);
  }

  template <typename T> static T to(ref v) {
    return (T)v.cast<number>()->n;
  }
};
")

(defobject "
struct empty_sequence final : object {
  type_t type() const final { return type_id<empty_sequence>; }
};

namespace cached {
  const var empty_sequence_o = obj<::ermine::empty_sequence>();
}
")

(defobject "
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
      ret = rt::cons(*rit, ret);
    return ret;
  }
  #endif
")

(defobject "
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
      data = rt::first(seq);
      seq = rt::rest(seq);
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
      return rt::first(run(thunk));

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
        return rt::rest(tail);
    }

    if (tail.is_nil())
      return rt::list();
    else
      return tail;
  }
};
")

(defobject "
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
      return rt::list();
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
      return rt::list();
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
")

(defobject "
struct d_list final : lambda_i, seekable_i {
  type_t type() const final { return type_id<d_list>; }

  var data;

  explicit d_list() : data(rt::list(rt::list())) { }

  explicit d_list(ref l) : data(l) { }

  var assoc(ref k, ref v) const {
    ref map = dissoc_aux(k);
    ref _keys = rt::first(map);
    ref _values = rt::rest(map);

    return obj<d_list>(rt::cons(rt::cons(k, _keys), rt::cons(v, _values)));
  }

  var dissoc_aux(ref k) const {
    ref _keys = rt::first(data);
    var _values = rt::rest(data);

    var new_keys;
    var new_values;

    for_each(i, _keys) {
      if (i != k)
      {
        new_keys = rt::cons(i, new_keys);
        new_values = rt::cons(rt::first(_values), new_values);
        _values = rt::rest(_values);
      }
    }

    return rt::cons(new_keys, new_values);
  }

  var dissoc(ref k) const {
    return obj<d_list>(dissoc_aux(k));
  }

  var val_at(ref args) const {
    ref key = rt::first(args);
    ref not_found = rt::first(rt::rest(args));

    ref _keys = rt::first(data);
    var _values = rt::rest(data);

    for_each(i, _keys) {
      if (key == i)
        return rt::first(_values);

      _values = rt::rest(_values);
    }

    if (!not_found.is_nil())
      return not_found;
    else
      return nil();
  }

  var invoke(ref args) const final {
    return val_at(args);
  }

  var vals () const { return rt::rest(data); }
  var keys () const { return rt::first(data); }

  virtual seekable_i* cast_seekable_i() { return this; }

  var cons(ref v) final {
    return rt::list(v, data);
  }

  var first() final {
    ref _keys = rt::first(data);
    ref _values = rt::rest(data);

    return rt::list(rt::first(_keys), rt::first(_values));
  }

  var rest() final {
    ref _keys = rt::first(data);
    ref _values = rt::rest(data);

    if (rt::rest(_keys).is_type(type_id<empty_sequence>))
      return rt::list();
    else
      return obj<d_list>(rt::cons(rt::rest(_keys), rt::rest(_values)));
  }
};

template <>
inline var obj<d_list>(var keys, var vals) {
  void* storage = ERMINE_ALLOCATOR::allocate<d_list>();

  return var(new(storage) d_list(rt::cons(keys, vals)));
}

#if !defined(ERMINE_MAP_TYPE)
typedef d_list map_t;
#endif
")

(defn assoc [m k v] "return m.cast<map_t>()->assoc(k, v);")
(defn dissoc [m k] "return m.cast<map_t>()->dissoc(k);")

(defn get [m & args] "return m.cast<map_t>()->val_at(args);")

(defn vals [m] "return m.cast<map_t>()->vals();")
(defn keys [m] "return m.cast<map_t>()->keys();")

(defobject "
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

  explicit string() : data(rt::list()) { }

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
    return obj<string>(rt::cons(x, data));
  }

  var first() final {
    return rt::first(data);
  }

  var rest() final {
    ref r = rt::rest(data);

    if (r.is_type(type_id<array_seq_t>) && rt::first(r) == obj<number>(0))
      return rt::list();
    else if (!r.is_type(type_id<empty_sequence>))
      return obj<string>(r);
    else
      return rt::list();
  }

  static var pack(ref s) {
    if (s.cast<string>()->data.is_type(type_id<array_seq_t>))
      return s.cast<string>()->data;

    size_t size = rt::count(s);
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
")

(defobject "
struct atomic final : deref_i {
  type_t type() const final { return type_id<atomic>; }

  mutex lock;
  var data;

  explicit atomic(ref d) : data(d) { }

  var swap(ref f, ref args) {
    lock_guard guard(lock);
    data = f.cast<lambda_i>()->invoke(rt::cons(data, args));
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
")

(defn atom [x] "return obj<atomic>(x)")

(defn swap! [a f & args] "return a.cast<atomic>()->swap(f, args);")
(defn reset! [a x] "return a.cast<atomic>()->reset(x);")

(defn lazy-seq! [f] "return obj<lazy_sequence>(f);")

(defn list [& s] "return s;")

(defn list? [x] "return x.is_type(type_id<sequence>) ? cached::true_o : cached::false_o;")

(defn seqable? [x] "return rt::is_seqable(x) ? cached::true_o : cached::false_o;")

(defn cons [x s] "return rt::cons(x, s);")

(defn first [s] "return rt::first(s);")
(defn rest [s] "return rt::rest(s);")

(defn second [s] (first (rest s)))

(defn nth [s ^number_t n] "return rt::nth(s, n);")
(defn nthrest [s ^number_t n] "return rt::nthrest(s, n);")

(defn reduce [f r s]
   "__result = r;

    for_each(i, s)
      __result = run(f, __result, i);")

(defn apply [f & s] "return rt::apply(f, s);")

(defn conj [coll & s] (reduce (fn [h v] (cons v h)) (if (nil? coll) (list) coll) s))

(defn reverse [s] (reduce (fn [h v] (cons v h)) (list) s))

(defn true? [x] "return (x) ? cached::true_o : cached::false_o;")
(defn false? [x] "return (!x) ? cached::true_o : cached::false_o;")

(defn nil? [x] "return x.is_nil() ? cached::true_o : cached::false_o;")

(defn not [x] "return (x) ? cached::false_o : cached::true_o;")

(defn = [& args]
  "var curr = rt::first(args);

   for_each(it, rt::rest(args)) {
     if (curr != it)
       return cached::false_o;
     curr = it;
   }

   return cached::true_o;")

(defn identical? [x y] "return (x.get() == y.get()) ? cached::true_o : cached::false_o;")

(defn < [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)) {
     if (number::to<real_t>(a) >= number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn > [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)) {
     if (number::to<real_t>(a) <= number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn >= [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)) {
     if (number::to<real_t>(a) < number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn <= [& args]
  "var a = rt::first(args);

   for_each(b, rt::rest(args)) {
     if (number::to<real_t>(a) > number::to<real_t>(b))
       return cached::false_o;
     a = b;
   }

   return cached::true_o;")

(defn count [s] "return obj<number>(rt::count(s))")

(defn zero? [x] (= x 0))
(defn pos? [x] (> x 0))
(defn neg? [x] (< x 0))

(defn + [& args]
  "real_t value(0.0);

   for_each(i, args)
     value = value + number::to<real_t>(i);

   __result = obj<number>(value);")

(defn - [& args]
  "__result = rt::first(args);
   real_t value = number::to<real_t>(__result);
   size_t count = 1;

   for_each(i, rt::rest(args)) {
     value = (value - number::to<real_t>(i));
     count++;
   }

   if (count == 1)
     value = value * real_t(-1.0);

   __result = obj<number>(value);")

(defn * [& args]
  "real_t value(1.0);

   for_each(i, args)
     value = (value * number::to<real_t>(i));

   __result = obj<number>(value);")

(defn / [& args]
  "__result = rt::first(args);
   real_t value = number::to<real_t>(__result);
   size_t count = 1;

   for_each(i, rt::rest(args)) {
     value = (value / number::to<real_t>(i));
     count++;
   }

   if (count == 1)
     value = real_t(1.0) / value;

   __result = obj<number>(value);")

(defn inc [x] (+ x 1))
(defn dec [x] (- x 1))

(defn min [& args]
  "__result = rt::first(args);

   for_each(i, rt::rest(args))
     if (number::to<real_t>(__result) > number::to<real_t>(i))
       __result = i;")

(defn max [& args]
  "__result = rt::first(args);

   for_each(i, rt::rest(args))
     if (number::to<real_t>(__result) < number::to<real_t>(i))
       __result = i;")

(defn rem [^number_t num ^number_t div] "return obj<number>((num % div));")

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

(defn range [^number_t n] "return rt::range(0, n)")

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

(defn drop [^number_t n coll] "return rt::nthrest(coll, n);")

(defn drop-while-aux [pred coll]
  "__result = coll;

   while (run(pred, __result))
     __result = rt::rest(__result);")

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
