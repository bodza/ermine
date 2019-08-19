class number final : public object {
  const real_t n;
public:

  type_t type() const final { return type_id<number>; }

  bool equals(ref o) const final {
    return (rt::abs(n - number::to<real_t>(o)) < real_epsilon);
  }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print(n);
  }
#endif

  template<typename T> explicit number(T x) : n(real_t(x)) {} 

  template<typename T> static T to(ref v){
    return (T)v.cast<number>()->n;
  }
};
