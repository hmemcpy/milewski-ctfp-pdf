variable (A B C D : Type)
-- snippet 1
variable (f : A → B)
-- snippet 2
variable (g : B → C)

-- snippet 3
#check g ∘ f

-- snippet 4
variable
  (f : A → B)
  (g : B → C)
  (h : C → D)
example : h ∘ (g ∘ f) = (h ∘ g) ∘ f := rfl

-- snippet 5
namespace snippet5
  def id : A → A := λ x => x
  #eval id Nat 10
end snippet5

-- snippet 6
example : f ∘ id = f := rfl
example : id ∘ f = f := rfl
