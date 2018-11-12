def extract[A](wa: Store[S, A]): A = wa match {
  case Store(f, s) => f(s)
}