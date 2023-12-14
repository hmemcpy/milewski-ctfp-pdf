_ :  (f : A → B)
     (g : B → C)
     (h : C → D)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → refl
