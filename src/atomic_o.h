class atomic final : public deref_i {
  mutex lock;
  var data;

  public:

  type_t type() const final { return type_id<atomic>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print("atom<");
    data.stream_console();
    rt::print('>');
  }
#endif

  explicit atomic(ref d) : data(d) {} 

  var swap(ref f, ref args){
    lock_guard guard(lock);
    data = f.cast<lambda_i>()->invoke(rt::cons(data, args));
    return data;
  }

  var reset(ref newval){
    lock_guard guard(lock);
    data = newval;
    return data;
  }

  var deref() final {
    lock_guard guard(lock);
    return data;
  }
};
