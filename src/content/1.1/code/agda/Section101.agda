module Section101 where

open import Data.Product using (_×_ ; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  A B C D a b : Set

{-                                                                   [snippet01] -}
f : A → B
f = {!!}

{-                                                                   [snippet02] -}
g : B → C
g = {!!}

{- g ∘ f                                                             [snippet03] -}

{-                                                                   [snippet04] -}
_ :  (f : A → B)
     (g : B → C)
     (h : C → D)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → refl

{-                                                                   [snippet05] -}
id : a → a
id x = x

module snippet06 {f : a → b} where
  _ : f ∘ id ≡ f  ×  id ∘ f ≡ f
  _ = refl , refl
