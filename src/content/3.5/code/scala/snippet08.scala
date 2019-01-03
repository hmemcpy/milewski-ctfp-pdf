def flatMap[A, B](ra: Reader[E, A])(k: A => Reader[E, B]): Reader[E, B] =
  Reader { e => ... }