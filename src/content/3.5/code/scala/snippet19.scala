implicit def stateMonad[S] = new Monad[State[S, ?]] {
  def flatMap[A, B](sa: State[S, A])(k: A => State[S, B]): State[S, B] =
    State { s =>
      val (a, s1) = runState(sa)(s)
      runState(k(a))(s1)
    }
  
  def pure[A](a: A): State[S, A] = State(s => (a, s))
}