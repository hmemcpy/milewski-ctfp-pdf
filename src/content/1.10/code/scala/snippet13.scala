def unConst[C, A]: Const[C, A] => C = {
  case Const(x) => x
}