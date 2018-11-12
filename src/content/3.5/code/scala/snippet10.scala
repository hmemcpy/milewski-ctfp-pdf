def flatMap[A, B](ra: Reader[E, A])(k: A => Reader[E, B]): Reader[E, B] =
  Reader { e =>
    val a = runReader(ra)(e)
    val rb = k(a)
    ...
  }