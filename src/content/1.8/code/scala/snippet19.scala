import kleisli._
def fmap[A, B](f: A => B): Writer[A] => Writer[B] =
  identity[Writer[A]] _ >=> (x => pure(f(x)))