instance
  _ : Bifunctor _⊎_
  _ = record { bimap = bimap  } where
    bimap : (a → c) → (b → d) → a ⊎ b → c ⊎ d
    bimap a→c _   (inj₁ a) = inj₁ (a→c a)
    bimap _   b→d (inj₂ b) = inj₂ (b→d b)
