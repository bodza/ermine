class empty_sequence final : public object {

  type_t type() const final { return type_id<empty_sequence>; }

#if !defined(FERRET_DISABLE_STD_OUT)
  void stream_console() const final {
    rt::print("()");
  }
#endif
};

namespace cached{
  const var empty_sequence_o = obj<::ferret::empty_sequence>();
}
