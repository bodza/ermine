#if !defined(FERRET_SAFE_MODE)
class fn_throttler : public lambda_i {
  var fn;
  elapsed_micros timer;
  real_t rate;
  bool blocking;

#if defined(FERRET_HARDWARE_ARDUINO)
  inline void _wait(real_t t) const{
    ::delayMicroseconds((number_t)t);
  }
#elif defined(FERRET_STD_LIB)
  inline void _wait(real_t t) const{
    auto duration = ::std::chrono::microseconds((number_t)t);
    ::std::this_thread::sleep_for(duration);
  }
#endif
  
  var exec(ref args){
    if (blocking)
      _wait(rate - timer.elapsed());

    if (timer.is_elapsed(rate)){
      timer.reset();
      return rt::apply(fn, args);
    }
    
    return nil();
  }
  
public:

  explicit fn_throttler(var f, real_t r, bool b) : fn(f), rate(r), blocking (b) { }

  var invoke(ref args) const final {
    return var((object*)this).cast<fn_throttler>()->exec(args);
  }
};
#endif
