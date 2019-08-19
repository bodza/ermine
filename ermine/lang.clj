(defmacro -> [x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       `(~(first form) ~x ~@(next form))
                       (list form x))]
        (recur threaded (next forms)))
      x)))

(defmacro ->> [x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       `(~(first form) ~@(next form) ~x)
                       (list form x))]
        (recur threaded (next forms)))
      x)))

(defmacro defn [name & body]
  `(def ~name (fn ~@body)))

(defmacro fn [& sig]
  (let [name (if (symbol? (first sig)) (first sig) nil)
        body (if name (rest sig) sig)]
    (if (vector? (first body))
      (let [[args & body] body]
        (new-fir-fn :name name :args args :body body))
      ;; handle multi arity function
      (let [fns   (map (fn* [body]
                            (let [[args & body] body]
                              (new-fir-fn :args args :body body)))
                       body)
            arity (->> (map first body)
                       (map (fn* [args] (filter #(not (= % '&)) args)))
                       (map #(count %)))
            fns   (->> (interleave arity fns)
                       (partition 2)
                       (sort-by first))
            fns   (if (->> fns last second second      ;; last arity arguments
                           (take-last 2) first (= '&)) ;; check &
                    (let [switch        (drop-last 1 fns)
                          [[_ default]] (take-last 1 fns)]
                      `(fir-defn-arity ~switch ~default))
                    `(fir-defn-arity ~fns))]
        (new-fir-fn :escape false :name name :body [fns])))))

(defmacro cxx [& body]
  (let [body (apply str body)]
    `((fn [] ~body))))

(defmacro defnative [name args & form]
  (let [includes (->> (filter #(seq? (nth % 2)) form)
                      (map #(cons (nth % 1) (apply list (nth % 2))))
                      (map (fn [form]
                             (let [[guard & headers] form]
                               (str "\n#if " guard "\n"
                                    (apply str (map #(str "#include \"" % "\"\n") headers))
                                    "#endif\n"))))
                      (map #(list 'native-declare %)))
        enabled (-> (symbol-conversion name) (str "_enabled") .toUpperCase)
        body (->> (map #(vector (second %) (last %)) form)
                  (map #(str "\n#if " (first %) "\n"
                             "#define " enabled "\n"
                             (second %)
                             "\n#endif\n"))
                  (apply str))
        body (str body
                  "\n#if !defined " enabled "\n"
                  "# error " (symbol-conversion name) " is not supported on this platform\n"
                  "#endif\n")
        pre-ample (->> (map #(vector (second %) (drop-last (drop 3 %))) form)
                       (remove #(empty? (second %)))
                       (map #(str "\n#if " (first %) "\n"
                                  (apply str (map (fn [line] (str line "\n")) (second %)))
                                  "\n#endif\n"))
                       (map #(list 'native-declare %)))]
    `(def ~name (fn ~args ~@includes ~@pre-ample ~body))))

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

#if !defined(ERMINE_DISABLE_STD_OUT)
  static void stream_console(ref coll) {
    var tail = rt::rest(coll);

    rt::print('(');
    if (tail)
      rt::first(coll).stream_console();

    for_each(i, tail) {
      rt::print(' ');
      i.stream_console();
    }
    rt::print(')');
  }
#endif
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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(value ? \"true\" : \"false\");
  }
#endif
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
struct pointer final : object {
  type_t type() const final { return type_id<pointer>; }

  void* payload;

  explicit pointer(void* p) : payload(p) { }

  bool equals(ref o) const final {
    return (payload == o.cast<pointer>()->payload);
  }

  template <typename T> static T* to_pointer(ref v) {
    return (T*)v.cast<pointer>()->payload;
  }

  template <typename T> static T& to_reference(ref v) {
    return *(pointer::to_pointer<T>(v));
  }
};
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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(n);
  }
#endif

  template <typename T> static T to(ref v) {
    return (T)v.cast<number>()->n;
  }
};
")

(defobject "
struct empty_sequence final : object {
  type_t type() const final { return type_id<empty_sequence>; }

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(\"()\");
  }
#endif
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

#if !defined(ERMINE_DISABLE_STD_OUT)
    void stream_console() const final {
      seekable_i::stream_console(var((object*)this));
    }
#endif

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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    seekable_i::stream_console(var((object*)this));
  }
#endif

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

  static var from(ref seq) {
    struct walk : lambda_i {
      var seq;

      explicit walk(ref s) : seq(s) { }

      var invoke(ref) const final {
        var tail = rt::rest(seq);

        if (tail.is_nil())
          return nil();
        else
          return obj<lazy_sequence>(rt::first(seq), obj<walk>(tail), true);
      }
    };

    return obj<lazy_sequence>(obj<walk>(seq), true);
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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    seekable_i::stream_console(var((object*)this));
  }
#endif

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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    seekable_i::stream_console(var((object*)this));
  }
#endif

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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    data.stream_console();
  }
#endif

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

(defn new-d-list-aux [keys vals] "return obj<d_list>(keys, vals);")

(defmacro new-d-list [& args]
  (let [kvs (partition 2 args)
        keys (map first kvs)
        vals (map second kvs)]
    `(new-d-list-aux (list ~@keys) (list ~@vals))))

(defn assoc [m k v] "return m.cast<map_t>()->assoc(k, v);")
(defn dissoc [m k] "return m.cast<map_t>()->dissoc(k);")

(defn get [m & args] "return m.cast<map_t>()->val_at(args);")

(defn vals [m] "return m.cast<map_t>()->vals();")
(defn keys [m] "return m.cast<map_t>()->keys();")

(defobject "
struct keyword final : lambda_i {
  type_t type() const final { return type_id<keyword>; }

  const number_t hash;

  static constexpr number_t hash_key(const char* key) {
    return *key ? (number_t)*key + hash_key(key + 1) : 0;
  }

  explicit keyword(number_t w) : hash(w) { }
  explicit keyword(const char* str): hash(hash_key(str)) { }

  bool equals(ref o) const final { return (hash == o.cast<keyword>()->hash); }

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(\"keyword#\");
    rt::print(hash);
  }
#endif

  var invoke(ref args) const final {
    ref map = rt::first(args);
    ref map_args = rt::cons(var((object*)this), rt::rest(args));

    if (map.is_type(type_id<map_t>))
      return map.cast<map_t>()->val_at(map_args);
    else
      return nil();
  }
};
")

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

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    var packed = string::pack(var((object*)this));
    char* str = string::c_str(packed);
    rt::print(str);
  }
#endif

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

(defn new-string
  ([] "")
  ([x] "return obj<string>(x);")
  ([x y] (new-string (concat x y)))
  ([x y & more] (new-string (concat x y) (apply concat more))))

(defobject "
struct atomic final : deref_i {
  type_t type() const final { return type_id<atomic>; }

  mutex lock;
  var data;

  explicit atomic(ref d) : data(d) { }

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(\"atom<\");
    data.stream_console();
    rt::print('>');
  }
#endif

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
(defn reset! [a newval] "return a.cast<atomic>()->reset(newval);")

(defobject "
#ifdef ERMINE_STD_LIB
struct async final : deref_i {
  type_t type() const final { return type_id<async>; }

  mutex lock;
  bool cached;
  var value;
  var fn;
  std::future<var> task;

  inline var exec() {
    return run(fn);
  }

  explicit async(ref f) : cached(false), value(nil()), fn(f), task(std::async(std::launch::async, [this]() { return exec(); })) { }

#if !defined(ERMINE_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(\"future<\");
    fn.stream_console();
    rt::print('>');
  }
#endif

  bool is_ready() {
    lock_guard guard(lock);
    if (cached)
      return true;
    return (task.wait_for(std::chrono::seconds(0)) == std::future_status::ready);
  }

  void get() {
    if (!cached) {
      value = task.get();
      cached = true;
    }
  }

  var deref() final {
    lock_guard guard(lock);
    get();
    return value;
  }
};
#endif
")

(defmacro future [& body] `(_future_ (fn [] ~@body)))

(defn _future_ [f] "return obj<async>(f);")

(defn future-done? [f]
  "if (f.cast<async>()->is_ready())
     return cached::true_o;
   else
     return cached::false_o;")

(defobject "
struct delayed final : deref_i {
  type_t type() const final { return type_id<delayed>; }

  mutex lock;
  var fn;
  var val;

  explicit delayed(ref f) : fn(f) { }

  var deref() final {
    lock_guard guard(lock);

    if (!fn.is_nil()) {
      val = fn.cast<lambda_i>()->invoke(nil());
      fn = nil();
    }

    return val;
  }
};
")

(defn _delay_ [f] "return obj<delayed>(f)")

(defmacro delay [& body] `(_delay_ (fn [] ~@body)))

(defn delay? [d]
  "if (d.is_type(type_id<delayed>))
     return cached::true_o;
   else
     return cached::false_o;")

(defn force [d] @d)

(defn new-lazy-seq
  ([thunk] "return obj<lazy_sequence>(thunk);")
  ([data thunk] "return obj<lazy_sequence>(data, thunk);"))

(defmacro lazy-seq [& body] `(new-lazy-seq (fn [] ~@body)))

(defn lazy-seq-cache [seq] "return lazy_sequence::from(seq);")

(defn list [& xs] "return xs;")

(defn list? [x]
  "if (x.is_type(type_id<sequence>))
     return cached::true_o;
   else
     return cached::false_o;")

(defn seqable? [coll]
  "if (rt::is_seqable(coll))
     return cached::true_o;
   else
     return cached::false_o;")

(defn cons [x seq] "return rt::cons(x, seq);")

(defn first [x] "return rt::first(x);")
(defn second [x] "return rt::first(rt::rest(x));")
(defn rest [x] "return rt::rest(x);")

(defn nth [coll ^number_t index] "return rt::nth(coll, index);")
(defn nthrest [coll ^number_t n] "return rt::nthrest(coll, n);")

(defn reduce
  ([f xs] (reduce f (first xs) (rest xs)))
  ([f acc coll]
   "__result = acc;
    for_each(i, coll)
      __result = run(f, __result, i);"))

(defn apply [f & argv] "return rt::apply(f, argv);")

(defn conj [coll & xs] (reduce (fn [h v] (cons v h)) (if (nil? coll) (list) coll) xs))

(defn reverse [s] (reduce (fn [h v] (cons v h)) (list) s))

(defn true? [x]
  "if (x)
     return cached::true_o;
   else
     return cached::false_o;")

(defn false? [x]
  "if (!x)
     return cached::true_o;
   else
     return cached::false_o;")

(defn nil? [x]
  "if (x.is_nil())
     return cached::true_o;
   else
     return cached::false_o;")

(defn not [x]
  "if (x)
     return cached::false_o;
   else
     return cached::true_o;")

(defn = [& args]
  "var curr = rt::first(args);
   for_each(it, rt::rest(args)) {
     if (curr != it)
       return cached::false_o;
     curr = it;
   }
   return cached::true_o;")

(defmacro not= [& test] `(not (= ~@test)))

(defn identical? [x y]
  "if (x.get() == y.get())
     return cached::true_o;
   else
     return cached::false_o;")

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

(defmacro and
  ([] true)
  ([x] x)
  ([x & next] `(if ~x (and ~@next) false)))

(defmacro or
  ([] nil)
  ([x] x)
  ([x & next] `(if ~x ~x (or ~@next))))

(defmacro when [test & body] `(if ~test (do ~@body)))

(defmacro cond [& clauses]
  (when clauses
    `(if ~(first clauses)
       ~(if (next clauses)
          (second clauses)
          (throw (Error. "cond requires an even number of forms")))
       (cond ~@(next (next clauses))))))

(defmacro if-let
  ([bindings then]
   `(if-let ~bindings ~then nil))
  ([bindings then else & oldform]
   (let [form (bindings 0) tst (bindings 1)]
     `(let* [temp# ~tst]
        (if temp#
          (let* [~form temp#]
            ~then)
          ~else)))))

(defmacro when-let [bindings & body]
  (let [form (bindings 0) tst (bindings 1)]
    `(let* [temp# ~tst]
       (when temp#
         (let* [~form temp#]
           ~@body)))))

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

(defn mod [num div]
  (let [m (rem num div)]
    (if (or (zero? m) (= (pos? num) (pos? div)))
      m
      (+ m div))))

(defn bit-and [^number_t x ^number_t y] "return obj<number>((x & y));")
(defn bit-not [^number_t x] "return obj<number>(~x);")
(defn bit-or [^number_t x ^number_t y] "return obj<number>((x | y));")
(defn bit-xor [^number_t x ^number_t y] "return obj<number>((x ^ y));")

(defn bit-shift-left [^number_t x ^number_t n] "return obj<number>((x << n));")
(defn bit-shift-right [^number_t x ^number_t n] "return obj<number>((x >> n));")

(defn identity [x] x)

(defn thread [f] "return obj<async>(f);")

(defmacro doseq [binding & body] `(_doseq_ ~(second binding) (fn [~(first binding)] ~@body)))

(defn _doseq_ [seq f] "for_each(it, seq) run(f, it);")

(defmacro dotimes [binding & body] `(_dotimes_ ~(second binding) (fn [~(first binding)] ~@body)))

(defn _dotimes_ [^number_t t f] "for (number_t i = 0; i < t; i++) run(f, obj<number>(i));")

(defn map [f coll]
  (lazy-seq
    (when (seqable? coll)
      (cons (f (first coll)) (map f (rest coll))))))

(defn range
  ([high] (range 0 high))
  ([^number_t low ^number_t high] "return rt::range(low, high)"))

(defn take [n coll]
  (lazy-seq
    (when (and (seqable? coll) (> n 0))
      (cons (first coll) (take (- n 1) (rest coll))))))

(defn take-while [pred s]
  (lazy-seq
    (when (and (seqable? s) (pred (first s)))
      (cons (first s) (take-while pred (rest s))))))

(defn drop [^number_t n coll] "return rt::nthrest(coll, n);")

(defn drop-while-aux [p c]
  "__result = c;

   while (run(p, __result))
     __result = rt::rest(__result);")

(defn drop-while [pred coll]
  (lazy-seq
    (drop-while-aux #(and (seqable? %) (pred (first %))) coll)))

(defn concat
  ([] (list))
  ([x]
    (when (seqable? x)
      (cons (first x) (lazy-seq (concat (rest x))))))
  ([x y]
    (if (seqable? x)
      (cons (first x) (lazy-seq (concat (rest x) y)))
      (concat y)))
  ([x y & more]
    (concat (concat x y) (apply concat more))))

(defn filter [pred coll]
  (lazy-seq
    (when (seqable? coll)
      (let [[f & r] coll]
        (if (pred f)
          (cons f (filter pred r))
          (filter pred r))))))

(defn partition
  ([n coll]
    (partition n n coll))
  ([n step coll]
    (lazy-seq
      (when (seqable? coll)
        (let [p (take n coll)]
          (when (= n (count p))
            (cons p (partition n step (nthrest coll step))))))))
  ([n step pad coll]
    (lazy-seq
      (when (seqable? coll)
        (let [p (take n coll)]
          (if (= n (count p))
            (cons p (partition n step pad (nthrest coll step)))
            (list (take n (concat p pad)))))))))

(defn every? [pred coll]
  "for_each(i, coll) {
     if (!run(pred, i))
       return cached::false_o;
   }
   return cached::true_o;")

(defn interleave [s1 s2]
  (lazy-seq
    (when (and (seqable? s1) (seqable? s2))
      (cons (first s1) (cons (first s2) (interleave (rest s1) (rest s2)))))))

(defn flatten [s]
  (lazy-seq
    (when (seqable? s)
      (if (seqable? (first s))
        (concat (flatten (first s)) (flatten (rest s)))
        (cons (first s) (flatten (rest s)))))))

(defn string? [s]
  "if (s.is_type(type_id<string>))
     return cached::true_o;
   else
     return cached::false_o;")

(defnative print [& more]
  (on "!defined(ERMINE_DISABLE_STD_OUT)"
      "if (more.is_nil())
         return nil();
       ref f = rt::first(more);
       f.stream_console();
       ref r = rt::rest(more);
       for_each(it, r) {
         rt::print(' ');
         it.stream_console();
       }
       return nil();"))

(defn println [& more]
  (apply print more)
  (cxx "rt::print((char)0xA);"))

(defn read-line []
  "char buf[ERMINE_IO_STREAM_SIZE] = {0};
   rt::read_line(buf, ERMINE_IO_STREAM_SIZE);
   return obj<string>(buf);")
