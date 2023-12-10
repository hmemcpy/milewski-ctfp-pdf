instance
  maybeFunctor : Functor Maybe
  maybeFunctor .fmap = λ f → λ where
    Nothing → Nothing
    (Just a) → Just (f a)
