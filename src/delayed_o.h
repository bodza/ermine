class delayed final : public deref_i {
  mutex lock;
  var fn;
  var val;

  public:

  type_t type() const final { return type_id<delayed>; }

  explicit delayed(ref f) : fn(f) {} 

  var deref() final {
    lock_guard guard(lock);
    if (!fn.is_nil()){
      val = fn.cast<lambda_i>()->invoke(nil());
      fn = nil();
    }
    return val;
  }
};
