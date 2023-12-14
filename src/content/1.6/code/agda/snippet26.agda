data Maybe (a : Set) : Set where
  Nothing  : Maybe a
  Just     : a → Maybe a
