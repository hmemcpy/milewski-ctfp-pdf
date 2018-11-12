sealed trait List[+E]
case object Nil extends List[Nothing]
final case class Cons[E](h: E, t: List[E]) extends List[E]