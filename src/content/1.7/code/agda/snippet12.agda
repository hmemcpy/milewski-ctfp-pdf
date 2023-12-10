instance
  pointEq : Eq Point
  pointEq ._==_ = eq
    where
    eq : Point → Point → Bool
    eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂
