class sequence final : public object, public seekable_i {
    const var next;
    const var data;
  public:

    type_t type() const final { return type_id<sequence>; }

#if !defined(FERRET_DISABLE_STD_OUT)
    void stream_console() const final {
      seekable_i::stream_console(var((object*)this));
    }
#endif

    explicit sequence(ref d = nil(), ref n = nil()) : next(n), data(d) {} 

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

    template <typename T>
    static T to(ref){
      T::unimplemented_function;
    }

    template <typename T>
    static var from(T){
      T::unimplemented_function; return nil();
    }

  };

  namespace runtime {
    inline var list() { 
      return cached::empty_sequence_o;
    }
    inline var list(ref v) { 
      return obj<sequence>(v,cached::empty_sequence_o);
    }
                      
    template <typename... Args>
    inline var list(ref first, Args const & ... args) { 
      return obj<sequence>(first, list(args...));
    }
  }

  #ifdef FERRET_STD_LIB
  typedef ::std::vector<var>  std_vector;

  template <> std_vector sequence::to(ref v) { 
    std_vector ret;
    for_each(i, v)
      ret.push_back(i);
    return ret;
  }

  template <> var sequence::from(std_vector v) { 
    var ret;
    std::vector<var>::reverse_iterator rit;
    // cppcheck-suppress postfixOperator
    for(rit = v.rbegin(); rit != v.rend(); rit++)
      ret = rt::cons(*rit,ret);
    return ret;
  }
  #endif
