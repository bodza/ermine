class keyword final : public lambda_i {
  const number_t hash;

  static constexpr number_t hash_key(const char * key){
    return *key ? (number_t)*key + hash_key(key + 1) : 0;
  }
  
public:

  type_t type() const final { return type_id<keyword>; }

  bool equals(ref o) const final { return (hash == o.cast<keyword>()->hash); }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print("keyword#");
    rt::print(hash);
  }
#endif

  explicit keyword(number_t w) : hash(w) {} 
  explicit keyword(const char * str): hash(hash_key(str)) { }

  var invoke(ref args) const final {
    ref map = rt::first(args);
    ref map_args = rt::cons(var((object*)this), rt::rest(args));

    if (map.is_type(type_id<map_t>)){
      return map.cast<map_t>()->val_at(map_args);
    }

    return nil();
  }
};
