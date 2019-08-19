class d_list final : public lambda_i, public seekable_i {

  var data;

  var dissoc_aux(ref k) const {
    ref _keys = rt::first(data);
    var _values = rt::rest(data);

    var new_keys;
    var new_values;

    for_each(i, _keys){
      if ( i == k)
        continue;
      new_keys = rt::cons(i, new_keys);
      new_values = rt::cons(rt::first(_values), new_values);
      _values = rt::rest(_values);
    }

    return rt::cons(new_keys,new_values);
  }

 public:

  type_t type() const final { return type_id<d_list>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    data.stream_console();
  }
#endif

  explicit d_list() : data(rt::list(rt::list())) { }
  explicit d_list(ref l) : data(l) { }

  var assoc(ref k, ref v) const {
    ref map = dissoc_aux(k);
    ref _keys = rt::first(map);
    ref _values = rt::rest(map);

    return obj<d_list>(rt::cons(rt::cons(k,_keys),
                                     rt::cons(v,_values)));
  }

  var dissoc(ref k) const {
    return obj<d_list>(dissoc_aux(k));
  }

  var val_at(ref args) const {
    ref key = rt::first(args);
    ref not_found = rt::first(rt::rest(args));

    ref _keys = rt::first(data);
    var _values = rt::rest(data);

    for_each(i, _keys){
      if (key == i)
        return rt::first(_values);

      _values = rt::rest(_values);
    }

    if (!not_found.is_nil()){
      return not_found;
    }else{
      return nil();  
    }
  }

  var invoke(ref args) const final {
    return val_at(args);
  }

  var vals () const { return rt::rest(data);}
  var keys () const { return rt::first(data);}

  virtual seekable_i* cast_seekable_i() { return this; }

  var cons(ref v) final {
    return rt::list(v,data);
  }

  var first() final {
    ref _keys = rt::first(data);
    ref _values = rt::rest(data);
    return rt::list(rt::first(_keys),rt::first(_values));
  }

  var rest() final {
    ref _keys = rt::first(data);
    ref _values = rt::rest(data);

    if(rt::rest(_keys).is_type(type_id<empty_sequence>))
      return rt::list();

    return obj<d_list>(rt::cons(rt::rest(_keys),rt::rest(_values)));
  }
};

template<>
inline var obj<d_list>(var keys, var vals) {
  void * storage = FERRET_ALLOCATOR::allocate<d_list>();
  return var(new(storage) d_list(rt::cons(keys,vals)));
}

#if !defined(FERRET_MAP_TYPE)
typedef d_list map_t;
#endif
