module Section108 where

open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a b c d : Set

{- 8.1 Bifunctors ----------------------------------------------------------------}
{-                                                                   [snippet01] -}
open import Function using (id; _∘_)

record Bifunctor (f : Set → Set → Set) : Set₁ where
  field
    bimap : (a → c) → (b → d) → f a b → f c d

  first : (a → c) → f a b → f c b
  first g = bimap g id

  second : (b → d) → f a b → f a d
  second h = bimap id h

  bimap-law : (a → c) → (b → d) → Set
  bimap-law g h =  (first g) ∘ (second h) ≡ bimap g h

-- open Bifunctor
{- 8.2 Product and Coproduct Bifunctors ------------------------------------------}
{-                                                                   [snippet02] -}
open import Data.Product using (_×_; _,_)

instance
  _ : Bifunctor _×_
  _ = record { bimap = bimap } where
      bimap : (a → c) → (b → d) → a × b → c × d
      bimap a→b c→d (a , c) = a→b a , c→d c

{-                                                                   [snippet03] -}
-- bimap : (a → c) → (b → d) → f a b → f c d

{-                                                                   [snippet04] -}
open import Data.Sum using (_⊎_; [_,_]; inj₁; inj₂)

-- standard Agda disjoint union

instance
  _ : Bifunctor _⊎_
  _ = record { bimap = bimap } where
    bimap : (a → c) → (b → d) → a ⊎ b → c ⊎ d
    bimap a→c _   (inj₁ a) = inj₁ (a→c a)
    bimap _   b→d (inj₂ b) = inj₂ (b→d b)

-- alternative, more closely following Haskell

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

instance
  _ : Bifunctor Either
  _ = record { bimap = bimap } where
      bimap : (a → c) → (b → d) → Either a b → Either c d
      bimap f _ (Left x) = Left (f x)
      bimap _ g (Right y) = Right (g y)

{- 8.3 Functorial Algebraic Data Types -------------------------------------------}
{-                                                                   [snippet05] -}
record Identity (a : Set) : Set where
  constructor mkId
  field identity : a

record Functor (f : Set → Set) : Set₁ where
  constructor mkFunctor
  field fmap : (a → b) → f a → f b

{-                                                                   [snippet06] -}
open Functor
open Identity

instance
  _ : Functor Identity
  _ = record { fmap = fm } where
      fm : (f : a → b) → Identity a → Identity b
      fm f (mkId ia) = mkId (f ia)

{-                                                                   [snippet07] -}
module snippet07 where
  data Maybe (a : Set) : Set where
    Nothing : Maybe a
    Just : a → Maybe a

data Const (c a : Set) : Set where
  mkConst : c → Const c a

instance
  _ : Functor (Const c)
  _ = record { fmap = fm } where
    fm : (f : a → b) → Const c a → Const c b
    fm _ (mkConst co) = mkConst co

{-                                                                   [snippet08] -}
open import Agda.Builtin.Unit

Maybe : Set → Set
Maybe a = Const ⊤ a ⊎ Identity a

Maybe′ : Set → Set
Maybe′ a = Either (Const ⊤ a) (Identity a)

