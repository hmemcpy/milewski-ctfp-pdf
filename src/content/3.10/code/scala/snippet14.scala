trait Coend[P[_, _]] {
  def paa[A]: P[A, A]
}