def foldr[A]: (A => A => A) => A => List[A] => A =
  f => z => {
    case x :: Nil => f(x)(z)
  }