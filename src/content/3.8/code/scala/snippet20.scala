sealed trait List[+E]
case object Nil extends List[Nothing]
case class Cons[E](h: E, t: List[E]) extends List[E]