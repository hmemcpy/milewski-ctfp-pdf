trait ProdP[P[_, _]] {
  def apply[A, B](f: A => B): P[A, B]
}