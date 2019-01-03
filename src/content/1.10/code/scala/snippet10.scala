def fmap[A, B](f: A => B): List[A] => List[B] = {
  case Nil => Nil
  case x :: xs => f(x) :: fmap(f)(xs)
}