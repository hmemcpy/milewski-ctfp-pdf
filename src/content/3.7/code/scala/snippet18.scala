def extract[A](wa: Stream[A]): A = wa match {
  case Stream(a, _) => a()
}