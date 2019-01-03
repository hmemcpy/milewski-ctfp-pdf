trait Monoid[M] {
  def combine(x: M, y: M): M
  def empty: M
}