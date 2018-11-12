def maybeTail[A]: List[A] => Option[List[A]] = {
  case Nil => None
  case Cons(x, xs) => Some(xs)
}