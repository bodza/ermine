class string final : public object, public seekable_i {
  var data;

  typedef array_seq<byte, number> array_seq_t;
  typedef array<byte> array_t;

  void from_char_pointer(const char * str, int length){
    data = obj<array_seq_t>((byte*)str, (size_t)(length + 1));

    var seq = (data.cast<array_seq_t>()->storage);
    auto & arr = value<array_t>::to_reference(seq).data;
    arr[length] = 0x00;
  }

public:

  type_t type() const final { return type_id<string>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    var packed = string::pack(var((object*)this));
    char* str = string::c_str(packed);
    rt::print(str);
  }
#endif

  explicit string() : data(rt::list()) {} 

  explicit string(ref s) : data(s) {}

  explicit string(const char * str) {
    int length = 0;
    for (length = 0; str[length] != 0x00; ++length);
    from_char_pointer(str, length);
  }

  explicit string(const char * str,number_t length) { from_char_pointer(str,length); }

  virtual seekable_i* cast_seekable_i() { return this; }

  var cons(ref x) final {
    return obj<string>(rt::cons(x,data));
  }

  var first() final {
    return rt::first(data);
  }

  var rest() final {
    ref r = rt::rest(data);

    if (r.is_type(type_id<array_seq_t>))
      if (rt::first(r) == obj<number>(0))
        return rt::list();

    if (!r.is_type(type_id<empty_sequence>))
      return obj<string>(r);

    return rt::list();
  }

  static var pack(ref s)  {
    if (s.cast<string>()->data.is_type(type_id<array_seq_t>))
      return s.cast<string>()->data;

    size_t size = rt::count(s);
    var packed_array = obj<value<array_t>>(size + 1);
    auto& packed_data = value<array_t>::to_reference(packed_array).data;

    size_t pos = 0;
    for_each(c, s){
      packed_data[pos] = number::to<byte>(c);
      pos++;
    }
    packed_data[pos] = 0x00;

    return obj<array_seq_t>(packed_array);
  }

  static char* c_str(ref s)  {
    var seq = (s.cast<array_seq_t>()->storage);
    auto & str = value<array<byte>>::to_reference(seq).data;
    return (char*) str;
  }

  template <typename T>
  static T to(ref){
    T::unimplemented_function;
  }
};

#ifdef FERRET_STD_LIB
template<>
inline var obj<string>(std::string s) {
  void * storage = FERRET_ALLOCATOR::allocate<string>();
  return var(new(storage) string(s.c_str(), (number_t)s.size()));
}

template <> ::std::string string::to(ref str) {
  var packed = string::pack(str);
  return std::string(string::c_str(packed));
}
#endif

#ifdef FERRET_HARDWARE_ARDUINO
template<>
inline var obj<string>(String s) {
  void * storage = FERRET_ALLOCATOR::allocate<string>();
  return var(new(storage) string(s.c_str(), (number_t)s.length()));
}

template <> String string::to(ref str) {
  var packed = string::pack(str);
  return String(string::c_str(packed));
}
#endif
