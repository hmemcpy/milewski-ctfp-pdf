object Monoid {
  implicit def listMonoid[A]: Monoid[List[A]] = new Monoid[List[A]] {
    def mempty: List[A] = List()
    def mappend(m1: List[A], m2: List[A]): List[A] = m1 ++ m2
  }
}