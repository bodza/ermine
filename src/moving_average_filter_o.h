template <typename T>
class moving_average_filter : public lambda_i {
  mutex lock;
  T alpha;
  mutable T avrg;

  var step(T data) {
    lock_guard guard(lock);
    avrg = ((alpha * data) + ((1. - alpha) * avrg));
    return obj<number>(avrg);
  }

public:

  explicit moving_average_filter(T a) : alpha(a), avrg(0) { }

  var invoke(ref args) const final {
    return var((object*)this).cast<moving_average_filter<T>>()
      ->step(number::to<T>(rt::first(args)));
  }
};
