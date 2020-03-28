type stream('a) =
  | Cons('a, Lazy.t(stream('a)));
