sealed trait List[+A]
case object Nil extends List[Nothing]
case class Cons[A](h: A, t: List[A]) extends List[A]