def fmap[A, B](f: A => B)(ma: M[A]): M[B] =
  flatMap(ma)(a => pure(f(a)))  