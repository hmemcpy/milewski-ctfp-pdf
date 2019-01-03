implicit val listMonad = new Monad[List] {
  def flatten[A](mma: List[List[A]]): List[A] =
    mma.reduce(_ ++ _)

  def pure[A](a: A): List[A] = List(a)
}