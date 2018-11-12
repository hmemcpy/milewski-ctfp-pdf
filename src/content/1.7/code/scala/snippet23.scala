def fmap[A, B]: (A => B) => (R => A) => (R => B) =
  f => g => f compose g