abstract class Adjunction[F[_], U[_]](
  implicit val F: Functor[F],
  val U: Representable[U]
){
  def unit[A](a: A): U[F[A]]

  def counit[A](a: F[U[A]]): A
}
