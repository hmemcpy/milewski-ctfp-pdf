def compose[A, B, C]: (A => B) => (C => A) => C => B =
  f => g => c => f(g(c))

def contramap[A, B, R](f: B => A)(g: Op[R, A]): Op[R, B] =
  flip(compose[A, R, B])(f)(g)
  // or just: (f andThen g)