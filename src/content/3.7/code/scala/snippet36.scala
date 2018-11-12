def duplicate[A](wa: Store[S, A]): Store[S, Store[S, A]] = wa match {
  case Store(f, s) => Store(Store(f), s)
}