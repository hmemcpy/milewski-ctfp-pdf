module Section102 where

open import Data.Integer using (ℤ; pos; +_)
open import Data.Nat using (ℕ; suc; _*_)
open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit

private variable
  a : Set

x : ℤ                                                             -- [snippet01] -}
x = + 0

module snippet02 where
  f : Bool → Bool                                                 -- [snippet02] -}
  f x = {!!}                                                      -- [snippet03] -}

{- { } denotes a "hole" and indicates that the program (proof) is incomplete.
   There are no partial functions in Agda per se---Agda is a "total" functional
   language. Thus, an Agda program that can be fully and successfully type-checked
   cannot have holes. There are no non-terminating function calls and recursion is
   limited to functions that provably terminate.                                 -}

module snippet04 where
  f : Bool → Bool
  f = {!!}
{-                                                                   [snippet05] -}
fact : ℕ → ℕ
fact 0 = 1
fact (suc n) = suc n * fact n
{-                                                                   [snippet06] -}
absurd : ⊥ → a
absurd = ⊥-elim
{-                                                                   [snippet07] -}
f44 : ⊤ → ℤ
f44 _ = + 44

module snippet08 where
  fInt : ℤ → ⊤
  fInt x = tt

module snippet09 where
  fInt : ℤ → ⊤
  fInt _ = tt

{-                                                                   [snippet10] -}
unit : a → ⊤
unit _ = tt
{-                                                                   [snippet11] -}
data Boolean : Set where
  True : Boolean
  False : Boolean
