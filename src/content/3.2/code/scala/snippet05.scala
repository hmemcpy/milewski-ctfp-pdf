abstract class Adjunction[F[_], U[_]](
  implicit val F: Functor[F],
  val U: Representable[U]
){
  // changed the order of parameters
  // to help Scala compiler infer types
  def leftAdjunct[A, B](a: A)(f: F[A] => B): U[B]

  def rightAdjunct[A, B](fa: F[A])(f: A => U[B]): B
}