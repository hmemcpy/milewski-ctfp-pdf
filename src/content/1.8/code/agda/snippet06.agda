instance
  _ : Functor Identity
  _ = record { fmap = fm } where
      fm : (f : a → b) → Identity a → Identity b
      fm f (mkId ia) = mkId (f ia)
