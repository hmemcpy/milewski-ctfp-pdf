sealed trait ListF[+E, +A]
case object NilF extends ListF[Nothing, Nothing]
case class ConsF[E, A](h: E, t: A) extends ListF[E, A]