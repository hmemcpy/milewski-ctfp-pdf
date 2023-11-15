open import Data.Integer using (ℤ; pos; +_)
open import Data.Nat using (ℕ; suc; _*_)
open import Data.Bool using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit

private variable
  A : Set

-- Sec. 2.3
x : ℤ
x = + 0

f : Bool -> Bool
f x = {!!}


{- { } denotes a "hole" and indicates that the program (proof) is
   incomplete. There are no partial functions in Agda per se---Agda is
   a "total" functional language. Thus, an Agda program that can be
   fully and successfully type-checked cannot have holes. There are
   no non-terminating function calls and recursion is limited to
   functions that provably terminate.
-}

f' : Bool -> Bool
f' = {!!}

fact : ℕ -> ℕ
fact 0 = 1
fact (suc n) = suc n * fact n

absurd : ⊥ -> A
absurd = ⊥-elim

f44 : ⊤ -> ℤ
f44 _ = + 44

fInt : ℤ -> ⊤
fInt x = tt

fInt' : ℤ -> ⊤
fInt' _ = tt

unit : A -> ⊤
unit _ = tt

data Boolean : Set where
  True : Boolean
  False : Boolean
