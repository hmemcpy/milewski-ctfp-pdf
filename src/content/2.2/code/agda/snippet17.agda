record ToString (a : Set) : Set where
  constructor toString
  field runToString : a → String
instance
  tostring : Contravariant ToString
  tostring .contramap f (toString g) = toString (g ∘ f)
