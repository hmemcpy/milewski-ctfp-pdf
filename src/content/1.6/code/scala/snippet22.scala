sealed trait OneOfThree[+A, +B, +C]
case class Sinistral[A](v: A) extends OneOfThree[A, Nothing, Nothing]
case class Medial[B](v: B) extends OneOfThree[Nothing, B, Nothing]
case class Dextral[C](v: C) extends OneOfThree[Nothing, Nothing, C]