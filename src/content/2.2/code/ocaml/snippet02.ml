let contramap (f : 'c_prime -> 'c) (u : 'c -> limD) : 'c_prime -> limD =
  Fun.compose u f
