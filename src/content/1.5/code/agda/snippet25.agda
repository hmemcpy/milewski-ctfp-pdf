data Either (A B : Set) : Set where
  Left : A → Either A B
  Right : B → Either A B
