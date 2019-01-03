sealed trait Pair[A, B]
case class P[A, B](a: A, b: B) extends Pair[A, B]