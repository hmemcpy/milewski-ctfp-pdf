
safe_head (ListFunctor.fmap f (x :: xs))
  = safe_head (f x :: f xs)
  = Some (f x)
