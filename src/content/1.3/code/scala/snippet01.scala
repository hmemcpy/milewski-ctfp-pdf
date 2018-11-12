trait Monoid[M] {
  def mempty: M
  def mappend(m1: M, m2: M): M
}