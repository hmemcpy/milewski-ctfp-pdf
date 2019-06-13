def unit[S, A](a: A): Reader[S, Product[S, A]] =
  Reader(s => Product((a, s)))