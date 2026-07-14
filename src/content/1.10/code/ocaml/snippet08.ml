OptFunctor.fmap f (safe_head (x :: xs))
  = OptFunctor.fmap f (Some x)
  = Some (f x)
