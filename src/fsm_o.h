class fsm final : public lambda_i {
  mutex lock;
  var state;
  var transitions;
public:

  inline fsm(ref s, ref t) : state(s), transitions(t){ }

  inline var invoke(ref) const final {
    return var((object*)this).cast<fsm>()->yield();
  }

  var yield() {
    lock_guard guard(lock);
    var value;

    if (state.is_type(type_id<lambda_i>))
      value = run(state);
    else
      value = state;

    var next = transitions.cast<lambda_i>()->invoke(rt::list(state));

    if (next.is_nil())
      next = state;

    state = next;
    return value;
  }
    
};
