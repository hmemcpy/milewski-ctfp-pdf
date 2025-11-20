(* As a reminder, this is not actual code *)
OptionFunctor.fmap f (safe_head [])
  = OptionFunctor.fmap f None
  = None
