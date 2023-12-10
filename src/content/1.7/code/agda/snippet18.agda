instance
  listFunc : Functor List
  listFunc .fmap _ Nil = Nil
  listFunc .fmap f (Cons x as) = Cons (f x) (fmap f as)
