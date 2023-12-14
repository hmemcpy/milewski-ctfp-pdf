-- Agda prohibits using the same name for type and data constructors.
data Pair (a b : Set) : Set where
  pair : a → b → Pair a b
