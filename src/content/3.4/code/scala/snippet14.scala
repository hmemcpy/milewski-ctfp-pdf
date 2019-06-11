trait Monad[M[_]] extends Functor[M] {
  def flatten[A](mma: M[M[A]]): M[A]
  def pure[A](a: A): M[A]
}