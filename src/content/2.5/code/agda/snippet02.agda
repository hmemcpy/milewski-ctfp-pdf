instance
  readerFunctor : Functor (Reader a)
  readerFunctor .fmap f (reader g) = reader (f ∘ g)
