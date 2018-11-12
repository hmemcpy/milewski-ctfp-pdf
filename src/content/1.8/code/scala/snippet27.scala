def flip[A, B, C]: (A => B => C) => (B => A => C) =
  f => y => x => f(x)(y)