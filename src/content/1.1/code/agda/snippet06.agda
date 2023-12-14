id : a → a
id x = x

_ : {f : a → b} → (f ∘ id ≡ f) × (id ∘ f ≡ f)
_ = refl , refl
