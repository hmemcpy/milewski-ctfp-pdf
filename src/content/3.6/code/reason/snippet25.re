let join: state('s, state('s, 'a)) => state('s, 'a) = (
  ssa => State(uncurry(run_state) <.> run_state(ssa)):
    state('s, state('s, 'a)) => state('s, 'a)
);
