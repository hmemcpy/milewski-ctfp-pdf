def contramap[A, B](f: B => A): Op[Boolean, A] => Op[Boolean, B] = {
  case Op(g) => Op(g compose f)
}