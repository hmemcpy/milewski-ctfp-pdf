def average[A](n: Int)
    (implicit fractional: Fractional[A]): Stream[A] => A = stm => {
  import fractional._
  sumS(n)(stm) / fromInt(n)
}