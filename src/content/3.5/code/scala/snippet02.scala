def flatMap[A, B](as: List[A])(k: A => List[B]): List[B] =
  flatten(fmap(k)(as))