variable (f : A → B)
variable (g : B → C)
variable (h : C → D)
example : h ∘ (g ∘ f) = (h ∘ g) ∘ f
  := sorry
