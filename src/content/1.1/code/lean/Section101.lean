variable (A B C D : Type)
-- snippet 1
variable (f : A → B)
-- snippet 2
variable (g : B → C)

-- snippet 3
#check g ∘ f

variable (f : A → B)
variable (g : B → C)
variable (h : C → D)
example : h ∘ (g ∘ f) = (h ∘ g) ∘ f
  := sorry
