sealed trait OneOfThree[+A, +B, +C]
final case class Sinistral[A](v: A) extends OneOfThree[A, Nothing, Nothing]
final case class Medial[B](v: B) extends OneOfThree[Nothing, B, Nothing]
final case class Dextral[C](v: C) extends OneOfThree[Nothing, Nothing, C]