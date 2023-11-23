data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b
