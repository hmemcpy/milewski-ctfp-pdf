implicit def opContravariant[A] = new Contravariant[Op[A, ?]] {
  def contramap[X, B](f: B => X)(h: Op[A, X]): Op[A, B] =
    h compose f
}