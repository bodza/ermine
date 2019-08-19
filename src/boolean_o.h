class boolean final : public object {
  const bool value;
public:

  type_t type() const final { return type_id<boolean>; }

  bool equals(ref o) const final {
    return (value == o.cast<boolean>()->container());
  }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    if (value)
      rt::print("true");
    else
      rt::print("false");
  }
#endif

  explicit boolean(bool b) : value(b) {} 

  bool container() const {
    return value;
  }
};

namespace cached{
  const var true_o = obj<::ferret::boolean>(true);
  const var false_o = obj<::ferret::boolean>(false);
}

var::operator bool() const {
  if (obj == nullptr)
    return false;
  else if (obj->type() == (type_t)type_id<boolean>)
    return cast<boolean>()->container();
  else
    return true;
}

bool var::equals (ref other) const {
  if (get() == other.get())
    return true;

  if (!is_nil() && !other.is_nil()){

    if (rt::is_seqable(*this) && rt::is_seqable(other))
      return seekable_i::equals(*this, other);
    else if (obj->type() != other.get()->type())
      return false;
    else
      return get()->equals(other);

  }else
    return false;
}
