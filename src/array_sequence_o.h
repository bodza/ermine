template<typename element_t, typename object_t>
class array_seq : public object , public seekable_i {
  size_t pos;

public:
  typedef array<element_t> array_t;
  typedef value<array_t> value_t;

  var storage;

  explicit array_seq(const element_t* src, size_t s = 0)
    : pos (0), storage(obj<value_t>(src, s)) { }

  explicit array_seq(var b, size_t p = 0) : pos(p), storage(b){ }

  explicit array_seq(size_t size) : pos(0), storage(obj<value_t>(size)){ }

  type_t type() const final { return type_id<array_seq>; }

#if !defined(FERRET_DISABLE_STD_OUT)
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

    return rt::list();
  }
};

template <>
class array<var> {
  size_t  _size{0};

  var* allocate(){
    var* storage = static_cast<var*>(FERRET_ALLOCATOR::allocate(_size * sizeof(var))) ;
    for(size_t i = 0; i < _size; i++)
      new (&storage[i]) var();
    return storage;
  }

public:

  var* data {nullptr};

  explicit inline array(size_t s = 0) : _size(s), data(allocate()) { }

  inline array(array&& m) :
    _size(m.size()), data(m.data) { m.data = nullptr; }

  inline array(array& m) : _size(m.size()), data(allocate()) {
    for(size_t i = 0; i < _size; i++)
      data[i] = m.data[i];
  }

  ~array(){
    for(size_t i = 0; i < size(); i++)
      (&data[i])->~var();
    FERRET_ALLOCATOR::free(data);
  }

  inline array& operator=(array&& x){
    data = x.data;
    _size = x._size;
    x.data = nullptr;
    return *this;
  }

  inline var& operator [](size_t idx)      { return data[idx]; }
  inline var operator [](size_t idx) const { return data[idx]; }

  inline var*    begin() const { return &data[0];      }
  inline var*    end()   const { return &data[_size];  }
  inline size_t  size()  const { return _size;         }
};

typedef array<var> var_array_t;
typedef value<var_array_t> var_array;
typedef array_seq<var,var> var_array_seq;

template<>
class array_seq<var,var> : public object , public seekable_i {
  size_t pos{0};

  inline static void into_aux(ref){ }

  template<typename... Args>
  inline static void into_aux(ref arr, ref first, Args... rest){
    auto& data = var_array::to_reference(arr);
    data[data.size() - sizeof...(rest) - 1] = first;
    into_aux(arr, rest...);
  }

public:
  var storage;

  explicit array_seq(var b, size_t p = 0) : pos(p), storage(b){ }

  type_t type() const final { return type_id<array_seq>; }

#if !defined(FERRET_DISABLE_STD_OUT)
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

    return rt::list();
  }

  template<typename... Args>
  static inline var into(Args... rest){
    var arr = obj<var_array>(sizeof...(rest));
    into_aux(arr, rest...);
    return obj<var_array_seq>(arr);
  }
};

namespace runtime{
  template<typename... Args>
  static inline var dense_list(Args... rest){
    return var_array_seq::into(rest...);
  }
}
