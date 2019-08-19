struct lambda_i : public object {
  virtual var invoke(ref args) const = 0;
  type_t type() const { return type_id<lambda_i>; }
};
