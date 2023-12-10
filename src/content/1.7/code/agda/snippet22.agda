instance
  fromR : Functor (λ (a : Set) → r → a)
  fromR .fmap f g = f ∘ g
