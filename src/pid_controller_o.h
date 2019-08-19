template <typename T>
class pid_controller : public lambda_i {
  mutex lock;
  mutable T setpoint;
  mutable T prev_error;
  mutable T total_error;
  mutable T error;
  mutable T result;
  mutable T input;

  T p;
  T i;
  T d;
  T maximum_output;
  T minimum_output;
  T maximum_input;
  T minimum_input;
  bool continuous;
  var setpoint_fn;

  void set_setpoint(ref p) {
    lock_guard guard(lock);
    T sp = number::to<T>(p);
    if (maximum_input > minimum_input) {
      if (sp > maximum_input) {
        setpoint = maximum_input;
      } else if (sp < minimum_input) {
        setpoint = minimum_input;
      } else {
        setpoint = sp;
      }
    } else {
      setpoint = sp;
    }
  }

  var step(ref in) {
    lock_guard guard(lock);
    input = number::to<T>(in);

    // Calculate the error signal
    error = setpoint - input;

    // If continuous is set to true allow wrap around
    if (continuous) {
      if (rt::abs(error) > ((maximum_input - minimum_input) / real_t(2))) {
        if (error > real_t(0)) {
          error = (error - maximum_input) + minimum_input;
        } else {
          error = (error + maximum_input) - minimum_input;
        }
      }
    }

    /*
     * Integrate the errors as long as the upcoming integrator does
     * not exceed the minimum and maximum output thresholds
     */
    if ((((total_error + error) * i) < maximum_output) &&
        (((total_error + error) * i) > minimum_output)) {
      total_error += error;
    }

    // Perform the primary PID calculation
    result = ((p * error) + (i * total_error) + (d * (error - prev_error)));

    // Set the current error to the previous error for the next cycle
    prev_error = error;

    // Make sure the final result is within bounds
    if (result > maximum_output) {
      result = maximum_output;
    } else if (result < minimum_output) {
      result = minimum_output;
    }

    return obj<number>(result);
  }

public:
  pid_controller(T kp, T ki, T kd,
                 T inMin, T inMax, T outMin, T outMax,
                 bool cont,
                 ref sp):
    p(kp),
    i(ki),
    d(kd),
    maximum_output(outMax),
    minimum_output(outMin),
    maximum_input(inMax),
    minimum_input(inMin),
    continuous(cont){

    if (sp.is_type(type_id<lambda_i>)){
      setpoint_fn = sp;
      set_setpoint(run(setpoint_fn));
    }else{
      set_setpoint(sp);
    }

    prev_error = 0;
    total_error = 0;
    error = 0;
    result = 0;
    input = 0;
  }

  var invoke(ref args) const final {
    if (!setpoint_fn.is_nil())
      var((object*)this).cast<pid_controller<T>>()
        ->set_setpoint(run(setpoint_fn));

    return var((object*)this).cast<pid_controller<T>>()
      ->step(rt::first(args));
  }
};
