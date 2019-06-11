def movingAvg[A](n: Int)(stm: Stream[A])
    (implicit fractional: Fractional[A]): Stream[A] =
  streamComonad.
    extend(average(n)(fractional))(stm)