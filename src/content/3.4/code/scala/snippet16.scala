def flatten[A, W: Monoid](wwa: Writer[W, Writer[W, A]]): Writer[W, A] =
  wwa match {
    case Writer((Writer((a, w2)), w1)) =>
      Writer(a, Monoid[W].combine(w1, w2))
  }