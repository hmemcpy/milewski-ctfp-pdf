open import Relation.Binary.PropositionalEquality using (_≡_)

record Monoid (m : Set) : Set where
  field
    unit     : m
    _⊕_      : m → m → m

    ⊕right-unit : ∀ (x : m) → x ⊕ unit ≡ x
    ⊕left-unit  : ∀ (x : m) → unit ⊕ x ≡ x
    ⊕assoc      : ∀ (x y z : m) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
