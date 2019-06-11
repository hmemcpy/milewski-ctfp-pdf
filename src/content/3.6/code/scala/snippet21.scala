implicit def state[S] = new Adjunction[Prod[S, ?], Reader[S, ?]] {
  def counit[A](a: Prod[S, Reader[S, A]]): A = a match {
    case Prod((Reader(f), s)) => f(s)
  }

  def unit[A](a: A): Reader[S, Prod[S, A]] =
    Reader(s => Prod((a, s)))
}