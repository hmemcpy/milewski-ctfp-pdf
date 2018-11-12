def counit[S, A](a: Prod[S, Reader[S, A]]): A = a match {
  case Prod((Reader(f), s)) => f(s)
}