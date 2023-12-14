data List (a : Set) : Set where
  Nil   : List a
  Cons  : a → List a → List a
