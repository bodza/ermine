class pointer final : public object {
  void * payload;
public:


  type_t type() const final { return type_id<pointer>; }

  bool equals(ref o) const final {
    return (payload == o.cast<pointer>()->payload);
  }

  explicit pointer(void* p) : payload(p) {}

  template<typename T> static T* to_pointer(ref v){
    return ((T *) v.cast<pointer>()->payload);
  }
  template<typename T> static T& to_reference(ref v){
    return (*(pointer::to_pointer<T>(v)));
  }
};
