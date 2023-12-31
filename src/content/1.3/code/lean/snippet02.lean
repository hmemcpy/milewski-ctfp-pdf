instance : Monoid String where
  mempty := ""
  mappend := λ x y => x ++ y
