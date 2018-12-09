trait Monoid[M] {
  def combine(m1: M, m2: M): M
  def empty: M
}