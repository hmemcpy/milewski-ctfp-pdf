{- Chapter 13. Free Monoids ------------------------------------------------------}

module Section203 where
open import Data.List using (List; _++_; []; [_]; _∷_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-identityʳ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable a b x : Set

-- CONSTRUCTION OF THE FREE MONOID --

{- Section 13.1. Free Monoid in Agda ---------------------------------------------}
{-                                                                   [snippet01] -}
record Monoid (a : Set) : Set where
  field
    mempty  :  a
    mappend :  a → a → a
    -- In Agda we can encode the laws that a monoid satisfies.
    idˡ    :  ∀ x → mappend mempty x ≡ x
    idʳ    :  ∀ x → mappend x mempty ≡ x
    assoc  :  ∀ x y z
              → mappend (mappend x y) z ≡ mappend x (mappend y z)

{-                                                                   [snippet02] -}
instance
  listMonoid : ∀ {a : Set} → Monoid (List a)
  listMonoid = record
                { mempty = []
                ; mappend = _++_
                ; idˡ = λ _ → refl
                ; idʳ = ++-identityʳ
                ; assoc = ++-assoc }
pattern [_,_] y z = y ∷ z ∷ []
{-                                                                   [snippet03] -}
_ : 2 * 3 ≡ 6
_ = refl  -- 2 * 3 and 6 are identified
_ : [ 2 ] ++ [ 3 ] ≡ [ 2 , 3 ]
_ = refl  -- whereas [ 2 ] ++ [ 3 ] and [6] are not identified

{- Section 13.2 Free Monoid Universal Construction -------------------------------}
{-                                                                   [snippet04] -}
module snippet04 where
  record homomorphism (A : Monoid a)(B : Monoid b) : Set where
    open Monoid A renaming (mappend to _*ᴬ_)
    open Monoid B renaming (mappend to _*ᴮ_)
    field
      h : a → b
      hom : ∀{x y} → h (x *ᴬ y) ≡ h x *ᴮ h y
{-                                                                   [snippet05] -}
_ : [ 2 ] ++ [ 3 ] ≡ [ 2 , 3 ]
_ = refl
{-                                                                   [snippet06] -}
_ : 2 * 3 ≡ 6
_ = refl
{-                                                                   [snippet07] -}
module snippet07  {m n : Monoid a}
                  {U   : {a : Set} → Monoid a → Set}
  where
  p : x → U m
  p = {!!}
{-                                                                   [snippet08] -}
  q : x → U n
  q = {!!}
{-                                                                   [snippet09] -}
  open snippet04
  -- h : m → n  -- This doesn't work because we haven't yet defined (in Agda)
  --            -- what it means to be a hom map from one monoid to another.
  --            -- We need a special arrow, say, _⇒_, of type Monoid a → Monoid b.
  --            -- Something like the following:
  --
  --            --   _⇒_ : Monoid a → Monoid b → Set
  --            --   m ⇒ n = a → b
  --
  --            --   h : m ⇒ n
  --            --   h = {!!}

{-                                                                   [snippet10] -}
  -- _ : q ≡ U h ∘ p
  -- _ = ?
