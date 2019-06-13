def counit[S, A](a: Product[S, Reader[S, A]]): A = a match {
  case Product((Reader(f), s)) => f(s)
}