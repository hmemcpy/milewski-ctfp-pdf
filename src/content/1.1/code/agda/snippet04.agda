open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

_ :  {A B C D : Set}
     (f : A → B)
     (g : B → C)
     (h : C → D)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → refl
