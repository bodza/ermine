namespace ferret{
  namespace runtime {
    inline bool is_seqable(ref coll){
      if(coll.cast<seekable_i>())
        return true;
      else
        return false;
    }
  
    inline var first(ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->first();
    }
  
    inline var rest(ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return nil();
      return seq.cast<seekable_i>()->rest();
    }
  
    inline var cons(ref x, ref seq){
      if (seq.is_nil() || seq.is_type(type_id<empty_sequence>))
        return rt::list(x);
      return seq.cast<seekable_i>()->cons(x);
    }
  
    var nth(var seq, number_t index){
      if (index < 0)
        return nil();
  
      for(number_t i = 0; i < index; i++)
        seq = rt::rest(seq);
      return rt::first(seq);
    }
  
    var nthrest(var seq, number_t index){
      for(number_t i = 0; i < index; i++)
        seq = rt::rest(seq);
  
      if (seq.is_nil())
        return rt::list(); 
  
      return seq;
    }
  
    inline size_t count(ref seq){
      size_t acc = 0;
  
      for(var tail = rt::rest(seq);
          !tail.is_nil();
          tail = rt::rest(tail))
        acc++;
  
      return acc;
    }
  
    inline var range(number_t low, number_t high){
      class seq : public lambda_i {
        number_t low, high;
      public:
        explicit seq(number_t l, number_t h) : low(l), high(h) { }
        var invoke(ref) const final {
          if (low < high)
            return obj<lazy_sequence>(obj<number>(low), obj<seq>((low + 1), high));
          return nil();
        }
      };
      return obj<lazy_sequence>(obj<seq>(low, high));
    }
  }
  template<typename T, typename... Args>
  inline var run(T const & fn, Args const & ... args) {
    return fn.invoke(rt::list(args...));
  }
  
  template<typename T>
  inline var run(T const & fn) {
    return fn.invoke(nil());
  }
  
  template<>
  inline var run(ref fn) {
    return fn.cast<lambda_i>()->invoke(nil());
  }
  
  template<typename... Args>
  inline var run(ref fn, Args const & ... args) {
    return fn.cast<lambda_i>()->invoke(rt::list(args...));
  }
  
  namespace runtime {
    inline var apply(ref f, ref argv){
      if (rt::rest(argv).is_type(type_id<empty_sequence>))
        return f.cast<lambda_i>()->invoke(rt::first(argv));
  
      struct{
        var operator()(ref seq) const {
          ref head = rt::first(seq);
  
          if (head.is_nil())
            return cached::empty_sequence_o;
  
          if (head.cast<seekable_i>())
            return head;
  
          return rt::cons(head, (*this)(rt::rest(seq)));
        }
      } spread;
  
      return f.cast<lambda_i>()->invoke(spread(argv));
    }
  }
}
