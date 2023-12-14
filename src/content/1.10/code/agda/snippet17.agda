instance
  readerFunctor : Functor (Reader e)
  readerFunctor .fmap f (reader g) = reader (f ∘ g)
