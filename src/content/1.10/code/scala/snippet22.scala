implicit def opContravariant[R] = new Contravariant[Op[R, ?]] {
  def contramap[A, B](f: B => A): Op[R, A] => Op[R, B] = {
    case Op(g) => Op(g compose f)
  }
}