record Monoid (m : Set) : Set where
  field
    mempty : m
    mappend : m -> m -> m
