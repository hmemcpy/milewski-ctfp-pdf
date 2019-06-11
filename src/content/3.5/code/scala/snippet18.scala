def flatMap[A, B](sa: State[S, A])(k: A => State[S, B]): State[S, B] =
  State { s =>
    val (a, s1) = runState(sa)(s)
    val sb = k(a)
    runState(sb)(s1)
  }