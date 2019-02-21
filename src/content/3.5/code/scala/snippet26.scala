def flatMap[A, B](ka: Cont[R, A])(kab: A => Cont[R, B]): Cont[R, B] =
  Cont(hb => ...)