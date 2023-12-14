_ :  (f : a → b) (g : b → c) (h : c → d)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → refl
