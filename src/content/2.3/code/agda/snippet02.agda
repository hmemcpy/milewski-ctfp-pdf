instance
  listMonoid : ∀ {a : Set} → Monoid (List a)
  listMonoid = record
                { mempty = []
                ; mappend = _++_
                ; idˡ = λ _ → refl
                ; idʳ = ++-identityʳ
                ; assoc = ++-assoc }
