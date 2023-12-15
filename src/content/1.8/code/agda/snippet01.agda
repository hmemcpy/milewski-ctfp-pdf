record Bifunctor (f : Set → Set → Set) : Set₁ where
  field
    bimap : (a → c) → (b → d) → f a b → f c d

  first : (a → c) → f a b → f c b
  first g = bimap g id

  second : (b → d) → f a b → f a d
  second h = bimap id h

  bimap-law : (a → c) → (b → d) → Set
  bimap-law g h =  (first g) ∘ (second h) ≡ bimap g h
