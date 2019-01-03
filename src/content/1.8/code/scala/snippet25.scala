trait Contravariant[F[_]] {
  def contramap[A, B](f: B => A)(fa: F[A]): F[B]
}