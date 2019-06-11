def length[A]: List[A] => Const[Int, A] = {
  case Nil => Const(0)
  case x :: xs => Const(1 + unConst(length(xs)))
}