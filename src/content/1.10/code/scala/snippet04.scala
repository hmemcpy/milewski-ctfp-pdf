def safeHead[A]: List[A] => Option[A] = {
  case Nil => None
  case x :: xs => Some(x)
}