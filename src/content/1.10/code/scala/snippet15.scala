def scam[A]: Const[Int, A] => Option[A] = {
  case Const(x) => None
}