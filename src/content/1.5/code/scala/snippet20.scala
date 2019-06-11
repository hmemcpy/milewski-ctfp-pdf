def factorizer[A, B, C]: (C => A) => (C => B) => (C => (A, B)) =
  p => q => x => (p(x), q(x))