class seekable_i {
  public:

    virtual var cons(ref x) = 0;
    virtual var first() = 0;
    virtual var rest() = 0;

#if !defined(FERRET_DISABLE_STD_OUT)
    static void stream_console(ref coll) {
      var tail = rt::rest(coll);

      rt::print('(');
      if (tail)
        rt::first(coll).stream_console();

      for_each(i, tail){
        rt::print(' ');
        i.stream_console();
      }
      rt::print(')');
    }
#endif

    static bool equals(var lhs, var rhs) {

      for(;;lhs = rt::rest(lhs), rhs = rt::rest(rhs)){

        ref lf = rt::first(lhs);
        ref rf = rt::first(rhs);

        if (lf.is_nil() && rf.is_nil())
          return true;
        
        if (lf != rf)
          return false;
      }
    }
  };
