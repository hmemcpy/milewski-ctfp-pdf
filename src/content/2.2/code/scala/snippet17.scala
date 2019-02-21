trait Contravariant[F[_]] {
  def contramap[A, B](fa: F[A])(f: B => A) : F[B]
}

class ToString[A](f: A => String) extends AnyVal 

implicit val contravariant = new Contravariant[ToString] {
  def contramap[A, B](fa: ToString[A])(f: B => A): ToString[B] =
    ToString(fa.f compose f)
}