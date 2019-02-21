implicit def writerMonad[W: Monoid] = new Functor[Writer[W, ?]] {
  def >=>[A, B, C](f: A => Writer[W, B], g: B => Writer[W, C]) =
    a => {
      val Writer((b, s1)) = f(a)
      val Writer((c, s2)) = g(b)
      Writer((c, Monoid[W].combine(s1, s2)))
    }

  def pure[A](a: A) =
    Writer(a, Monoid[W].empty)
}

object kleisliSyntax {
  //allows us to use >=> as an infix operator
  implicit class MonadOps[M[_], A, B](m1: A => M[B]) {
    def >=>[C](m2: B => M[C])(implicit m: Monad[M]): A => M[C] = {
      m.>=>(m1, m2)
    }
  }
}