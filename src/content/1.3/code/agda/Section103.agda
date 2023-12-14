module Section103 where

open import Data.String using (String; _++_)

{-                                                                   [snippet01] -}
record Monoid (m : Set) : Set where
  field
    mempty : m
    mappend : m -> m -> m

{-                                                                   [snippet02] -}
instance
  StringMonoid : Monoid String
  StringMonoid = record { mempty = ""; mappend = _++_ }
