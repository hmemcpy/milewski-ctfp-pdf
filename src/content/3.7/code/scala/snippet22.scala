def sumS[A](n: Int)(stm: Stream[A])(implicit numeric: Numeric[A]): A =
  stm match {
    case Stream(a, as) =>
      import numeric._
      if (n <= 0) zero else a() + sumS(n - 1)(as())
  }