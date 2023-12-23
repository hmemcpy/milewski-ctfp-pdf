{- 7 Functors --------------------------------------------------------------------}
{- If a morphism f in ℂ connects object a to object b, f : a → b, then
   the image of f in 𝔻, F f, will connect the image of a to the image of
   b: F f : F a → F b.

   𝔻     F a --- F f ---→ F b
          ↑                ↑
          |                |
          |                |
          |                |
   ℂ      a ----- f -----→ b
                                                                                 -}
{-# OPTIONS --guardedness --sized-types #-}

module Section107 where

open import Data.Bool using (Bool; _∧_)
open import Data.Product.Base as P using (_×_; _,_; <_,_>)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Float using (Float; _≟_)
open import Level using (Level)
open import Codata.Sized.Stream using (Stream; _∷_; iterate)
open import Relation.Nullary.Decidable using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Size using (Size; ∞)
open import Codata.Sized.Thunk as Thunk using (Thunk; force)

private variable
  a b c r : Set
  i : Size

{- 7.1 Functors in Programming ---------------------------------------------------}
{- 7.1.1 The Maybe Functor -------------------------------------------------------}
{-                                                                   [snippet01] -}
data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a → Maybe a
{-                                                                   [snippet02] -}
f : a → b
f = {!!}
{-                                                                   [snippet03] -}
f' : Maybe a → Maybe b
f' Nothing = Nothing
f' (Just x) = Just (f x)

module snippet04 where
  fmap : (a → b) → Maybe a → Maybe b                              -- [snippet05] -}
  fmap _ Nothing = Nothing                                        -- [snippet06] -}
  fmap f (Just x) = Just (f x)

{- 7.1.2 Equational Reasoning ----------------------------------------------------}
{-                                                                   [snippet07] -}
id : a → a
id x = x

module snippet08 where
  open snippet04
  fmap-id : (x : Maybe a) → fmap id x ≡ id x
  fmap-id Nothing = refl
  fmap-id (Just x) = refl

-- non-dependent function composition
_∘_ : (b → c) → (a → b) → a → c
f ∘ g = λ x → f (g x)

module snippet09 {f : a → b}{g : b → c} where
  open snippet04
  _ : fmap (g ∘ f) ≡ fmap g ∘ fmap f
  _ = {!!}  -- We can't prove this in pure Martin-Löf Type Theory;
            -- but we can prove the following extensional version:
  fmap-∘ : ∀(x : Maybe a) → fmap (g ∘ f) x ≡ (fmap g ∘ fmap f) x
  fmap-∘ Nothing = refl
  fmap-∘ (Just x) = refl

{- 7.1.4 Typeclasses -------------------------------------------------------------}
{-                                                                   [snippet10] -}
record Eq (a : Set) : Set where
  field _==_ : a → a → Bool

open Eq ⦃...⦄

{-                                                                   [snippet11] -}
data Point : Set where
  Pt : Float → Float → Point
{-                                                                   [snippet12] -}
instance
  floatEq : Eq Float
  floatEq ._==_ = λ x y → does (x ≟ y)

  pointEq : Eq Point
  pointEq ._==_ = eq
    where
    eq : Point → Point → Bool
    eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂

{-                                                                   [snippet13] -}
record Functor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b
{-                                                                   [snippet14] -}
open Functor ⦃...⦄
instance
  maybeFunctor : Functor Maybe
  maybeFunctor .fmap = λ f → λ where
    Nothing → Nothing
    (Just a) → Just (f a)

{- 7.1.6 The List Functor --------------------------------------------------------}
module snippet15 where
  data List (a : Set) : Set where
    Nil  : List a
    Cons : a → List a → List a
  {-                                                                 [snippet18] -}
  instance
    listFunc : Functor List
    listFunc .fmap _ Nil = Nil
    listFunc .fmap f (Cons x as) = Cons (f x) (fmap f as)         -- [snippet17] -}

    fromR : Functor λ a → (r → a)
    fromR .fmap = _∘_

{- 7.1.7 The Reader Functor ------------------------------------------------------}
{-                                                                   [snippet22] -}
instance
  fromR : Functor (λ (a : Set) → r → a)
  fromR .fmap f g = f ∘ g
  -- fromR .fmap f g = _∘_ f g                                    -- [snippet23] -}
  -- fromR .fmap = _∘_                                            -- [snippet24] -}

{- 7.2 Functions as Containers ---------------------------------------------------}
{-                                                                   [snippet25] -}
nats : Stream ℕ ∞
nats = iterate suc zero
{-                                                                   [snippet26] -}
data Const (c a : Set) : Set where
  mkConst : c → Const c a
{- The type of fmap for this type constructor is:
  fmap : (a → b) → Const c a → Const c b                             [snippet27] -}
{-                                                                   [snippet28] -}
instance
  constFunc : Functor (Const c)
  constFunc .fmap _ (mkConst c) = mkConst c

{- 7.3 Functor Composition -------------------------------------------------------}
open import Agda.Builtin.List
maybeTail : List a → Maybe (List a)
maybeTail [] = Nothing
maybeTail (x ∷ xs) = Just xs

open import Agda.Builtin.Int
open import Data.Integer
square : Int → Int
square x = x * x

mis : Maybe (List Int)
mis = Just (+ 1 ∷ + 2 ∷ + 3 ∷ [])
instance
  ListFunc : Functor List
  ListFunc .fmap _ [] = []
  ListFunc .fmap f (x ∷ as) = (f x) ∷ (fmap f as)

mis2 : Maybe (List Int)
mis2 = fmap (fmap square) mis

mis2' : Maybe (List Int)
mis2' = (fmap ∘ fmap) square mis
