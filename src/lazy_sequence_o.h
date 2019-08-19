class lazy_sequence final : public object, public seekable_i {
  mutex lock;
  bool cache;
  var thunk;
  var data;
  var seq;

  void yield(){
    if (thunk.is_nil())
      return;

    seq = run(thunk);

    if (data.is_nil()){
      data = rt::first(seq);
      seq = rt::rest(seq);
    }

    thunk = nil();
  }

public:

  type_t type() const final { return type_id<lazy_sequence>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    seekable_i::stream_console(var((object*)this));
  }
#endif

  explicit lazy_sequence(ref t, bool c = false) : cache(c), thunk(t) {}
  explicit lazy_sequence(ref d, ref t, bool c = false) : cache(c), thunk(t), data(d) {}

  virtual seekable_i* cast_seekable_i() { return this; }

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
    else
      if (data.is_nil())
        return rt::first(run(thunk));
    return data;
  }
    
  var rest() final {
    lock_guard guard(lock);
    var tail;

    if (cache){
      yield();
      tail = seq;
    }else{
      tail = run(thunk);
      if (data.is_nil())
        return rt::rest(tail);
    }

    if (tail.is_nil())
      return rt::list();

    return tail;
  }

  static var from(ref seq) {
    class walk : public lambda_i {
      var seq;
    public:
      explicit walk(ref s) : seq(s) { }
      var invoke(ref) const final {
        var tail = rt::rest(seq);
        if (tail.is_nil())
          return nil();

        return obj<lazy_sequence>(rt::first(seq), obj<walk>(tail), true);
      }
    };

    return obj<lazy_sequence>(obj<walk>(seq), true);
  }
};
