def unit[S, A](a: A): Reader[S, Prod[S, A]] =
  Reader(s => Prod((a, s)))