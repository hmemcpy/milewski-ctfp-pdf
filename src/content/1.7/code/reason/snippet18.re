let rec fmap = f =>
  fun
  | Nil => Nil
  | Cons(x, xs) => Cons(f(x), fmap(f, xs));
