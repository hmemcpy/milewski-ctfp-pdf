class Monoid (m : Type) where
  mempty : m
  mappend : m → m → m
