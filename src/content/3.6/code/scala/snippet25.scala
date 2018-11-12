def join[S, A]: State[S, State[S, A]] => State[S, A] =
  ssa => {
    State(
      Function.uncurried(runState[S, A])
        .tupled
        .compose(runState(ssa))
    )
  }