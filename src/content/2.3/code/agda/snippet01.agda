record Monoid (a : Set) : Set where
  field
    mempty  :  a
    mappend :  a → a → a
    -- In Agda we can encode the laws that a monoid satisfies.
    idˡ    :  ∀ x → mappend mempty x ≡ x
    idʳ    :  ∀ x → mappend x mempty ≡ x
    assoc  :  ∀ x y z
              → mappend (mappend x y) z ≡ mappend x (mappend y z)
