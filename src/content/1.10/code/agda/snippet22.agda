instance
  opContra : Contravariant (Op r)
  opContra .contramap f (op g) = op (g ∘ f)
