implicit def opContravariant[R] = new Contravariant[R, ?] {
  def contramap[A, B](f: B => A)(g: Op[R, A]): Op[R, B] =
    g compose f
}