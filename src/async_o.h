#ifdef FERRET_STD_LIB
class async final : public deref_i {
  mutex lock;
  bool cached;
  var value;
  var fn;
  std::future<var> task;

  inline var exec() {
    return run(fn);
  }

  public:

  explicit async(ref f) :
    cached(false), value(nil()), fn(f), 
    task(std::async(std::launch::async, [this](){ return exec(); })){ }

  type_t type() const final { return type_id<async>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print("future<");
    fn.stream_console();
    rt::print('>');
  }
#endif

  bool is_ready(){
    lock_guard guard(lock);
    if (cached)
      return true;
    return task.wait_for(std::chrono::seconds(0)) == std::future_status::ready;
  }

  void get(){
    if (!cached){
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
