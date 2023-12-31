variable
  (f : A → B)
  (g : B → C)
  (h : C → D)
example : h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl
