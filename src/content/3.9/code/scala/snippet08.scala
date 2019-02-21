implicit def storeComonad[S] = new Comonad[Store[S, ?]] {
  def extract[A](wa: Store[S, A]): A = wa match {
    case Store(f, s) => f(s)
  }
  
  def duplicate[A](wa: Store[S, A]): Store[S, Store[S, A]] = wa match {
    case Store(f, s) => Store(Store(f), s)
  }
}