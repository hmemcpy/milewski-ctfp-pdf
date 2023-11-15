open import Data.String using (String; _++_)

record Monoid (m : Set) : Set where
  field
    mempty : m
    mappend : m -> m -> m

instance
  StringMonoid : Monoid String
  StringMonoid = record
    { mempty = ""
    ; mappend = _++_
    }
