template <typename T>
class value final : public object {
  T payload;
public:

  type_t type() const final { return type_id<value>; }

  template <typename... Args>
  explicit value(Args&&... args) : payload(static_cast<Args&&>(args)...) { } 

  T to_value() const {
    return payload;
  }

  static T to_value(ref v){
    return v.cast<value<T>>()->payload;
  }
  
  T & to_reference() {
    return payload;
  }
    
  static T & to_reference(ref v) {
    return v.cast<value<T>>()->to_reference();
  }  
};

typedef value<matrix> matrix_t;
