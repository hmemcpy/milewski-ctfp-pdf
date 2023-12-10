record Functor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b
