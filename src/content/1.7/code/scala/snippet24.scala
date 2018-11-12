def fmap[A, B]: (A => B) => (R => A) => (R => B) =
  _ compose