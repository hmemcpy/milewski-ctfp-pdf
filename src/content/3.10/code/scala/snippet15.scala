trait SumP[P[_, _]] {
  def f[A, B]: B => A
  def pab[A, B]: P[A, B]
}