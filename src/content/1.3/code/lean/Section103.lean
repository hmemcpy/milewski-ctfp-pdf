-- snippet 01
class Monoid (m : Type) where
  mempty : m
  mappend : m → m → m

-- snippet 02
instance : Monoid String where
  mempty := ""
  mappend := λ x y => x ++ y
