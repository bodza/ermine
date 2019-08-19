#if !defined(FERRET_SAFE_MODE)
class elapsed_micros : public object {
  mutex lock;
  unsigned long us;

#if defined(FERRET_HARDWARE_ARDUINO)
  inline unsigned long now() const{
    return ::micros();
  }
#elif defined(FERRET_STD_LIB)
  inline unsigned long now() const{
    auto now = ::std::chrono::high_resolution_clock::now();
    auto epoch = now.time_since_epoch();
    return (unsigned long)::std::chrono::duration_cast<::std::chrono::microseconds>(epoch).count();
  }
#endif

 public:

  elapsed_micros(void) { us = now(); }

  void reset() {
    lock_guard guard(lock);
    us = now();
  }

  type_t type() const { return type_id<elapsed_micros>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const {
    rt::print("micros#");
    rt::print(elapsed());
  }
#endif

  inline real_t elapsed() const { return (real_t)(now() - us); }
  inline bool is_elapsed(real_t t) const { return (elapsed() >= t); }
};
#endif
