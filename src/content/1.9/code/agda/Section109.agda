module Section109 where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Float using (Float) renaming (_<ᵇ_ to _<ᶠᵇ_)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Nat.Base as ℕ using ()
open import Data.Product using (_×_; _,_; Σ-syntax) renaming (dmap′ to _⟨∘⟩_)
open import Data.String using (String; _++_)
open import Function using (_∘_; _∘₂_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


private variable a b c d e : Set

{- 9 Function Types  -------------------------------------------------------------}

{- 9.1 Universal Construction ----------------------------------------------------}
{- The product z × a is an object, and we can pick as our application morphism an
   arrow g from that object to b. In Set, g would be the function that maps every
   pair (f, x) to f x.

           _______
     ---  |       |               ___
    | z | | z × a |  ---- g ---> | b |
     ---  |       |               ---
           -------
             ---
            | a |
             ---

                 NO PRODUCT TYPE  ⇒  NO FUNCTION TYPE.
                _______
     ---       |       |
    | z |      | z × a |__
     ---       |       |  -- g __
      |         -------          \
      |            |              ↘ ---
      h          h × id            | b |
      |            |              ↗ ---
      |      _____ ↓ _____       /
   -- ↓ --  |             |  eval
  | a ⇒ b | | (a ⇒ b) × a |_/
   -------  |             |
             -------------
                  ---
                 | a |
                  ---

   A *function object* from a to b is an object a ⇒ b together with the morphism

                  eval : ((a ⇒ b) × a) → b

    such that for any other object z with a morphism g : z × a → b,

                  ∃! h : z → (a ⇒ b)

    that factors g through eval:

                  g = eval ∘ (h × id).

   (We prove existence of such h below, after we define the "curry" and
   "factorizer" functions.)
                                                                                 -}


{- 9.2 Currying ------------------------------------------------------------------}
{- a → (b → c)                                                       [snippet01] -}
{- a → b → c                                                         [snippet02] -}
{-                                                                   [snippet03] -}
catstr : String → String → String
catstr s s' = s ++ s'
{-                                                                   [snippet04] -}
catstr' : String → String → String
catstr' s = λ s' → s ++ s'
{-                                                                   [snippet05] -}
greet : String → String
greet = catstr "Hello "
{- a × b → c                                                         [snippet06] -}
{-                                                                   [snippet07] -}
curry : (a × b → c) → a → b → c
curry f a b = f (a , b)
{-                                                                   [snippet08] -}
uncurry : (a → b → c) → a × b → c
uncurry f (a , b) = f a b
{-                                                                   [snippet09] -}
factorizer : (a × b → c) → a → (b → c)
factorizer g = λ x → λ y → g (x , y)
{-                                                                   [snippet13] -}
eval : ((a → b) × a) → b
eval (f , a) = f a

→-univ-prop-existence' :  ∀ (z : Set)(g : z × a → b)
  →                       Σ[ h ∈ (z → (a → b)) ]  g ≡ eval ∘ h ⟨∘⟩ id
→-univ-prop-existence' z g = factorizer g , refl

{- 9.3 Exponentials --------------------------------------------------------------}

{- 9.4 Cartesian Closed Categories -----------------------------------------------}

{- 9.5 Exponentials and Algebraic Data Types -------------------------------------}

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

-- Define a boolean version of less than for ℤ, as is done in the standard
-- library for weak inequality, _≤ᵇ_.
open import Agda.Builtin.Int public
  using () renaming ( Int     to ℤ
                    ; pos     to +_        -- "+ n"      stands for "n"
                    ; negsuc  to -[1+_] )  -- "-[1+ n ]" stands for "- (1 + n)"
_<ᵇ_ : ℤ → ℤ → Bool
-[1+ m ] <ᵇ -[1+ n ] = n ℕ.<ᵇ m
(+ m)    <ᵇ -[1+ n ] = false
-[1+ m ] <ᵇ (+ n)    = true
(+ m)    <ᵇ (+ n)    = m ℕ.<ᵇ n
{-                                                                   [snippet10] -}
f : Either ℤ Float → String
{-                                                                   [snippet11] -}
f (Left n) = if (n <ᵇ 0ℤ) then "Negative Int" else "Nonnegative Int"
f (Right n) = if (n <ᶠᵇ 0.0) then "Negative Float" else "Nonnegative Float"

{- 9.6 Curry-Howard Isomorphism --------------------------------------------------}
{- _ : Either a b → a                                                [snippet14] -}
{- absurd : ⊥ → a                                                    [snippet15] -}
absurd : ⊥ → a
absurd ()
