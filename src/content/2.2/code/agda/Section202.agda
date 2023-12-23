{- Chapter 12. Limits and Colimits -}

module Section202 where

open import Agda.Builtin.Float
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Integer
open import Data.String
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_)
-- private variable a b c c' d LimD : Set

_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)


module snippet01 {a b c c' : Set} where
  p : c → a; q : c → b; m : c' → c
  p = {!!}; q = {!!}; m = {!!}
  p' : c' → a; q' : c' → b
  {-                                                                 [snippet01] -}
  p' = p ∘ m
  q' = q ∘ m

{-                  Lim[D] is the universal (or "best") cone for D.              -}

{- 12.1 Limit as a Natural Isomorphism  ------------------------------------------}

module snippet02 {c c' LimD : Set} where
  {-                                                                 [snippet02] -}
  contramap : (c' → c) → (c -> LimD) → (c' -> LimD)
  contramap f u = u ∘ f

{- 12.2 Examples of Limits  ------------------------------------------------------}

module snippet03 {a b c : Set} where
  f : a → b
  g : a → b
  f = {!!}; g = {!!}

{- To build a cone over this diagram, we add the apex, c and two projections:

               c
             /   \
            p     q
           /       \
          /  _ f _  \
         ↓ /       ↘ ↓
         a --- g --→ b
                                                                     [snippet04] -}
  p : c → a
  q : c → b
  p = {!!}; q = {!!}
{-                                                                   [snippet05] -}
  _ : q ≡ f ∘ p
  _ = {!!}
  _ : q ≡ g ∘ p
  _ = {!!}
{-                                                                   [snippet06] -}
  _ : f ∘ p ≡ g ∘ p
  _ = {!!}

module snippet07 where
  f : ℤ × ℤ → ℤ
  g : ℤ × ℤ → ℤ
  {-                                                                 [snippet07] -}
  f (x , y) = + 2 * y + x
  g (x , y) = y - x

  p : ℤ → ℤ × ℤ
  {-                                                                 [snippet08] -}
  p t = (t , - (+ 2 * t))

  p' : ⊤ → ℤ × ℤ
  {-                                                                 [snippet09] -}
  _ : f ∘ p' ≡ g ∘ p'
  _ = {!!}
  {-                                                                 [snippet10] -}
  p' tt = (0ℤ , 0ℤ)

  h : ⊤ → ℤ
  {-                                                                 [snippet11] -}
  _ : p' ≡ p ∘ h
  _ = {!!}
  {-                                                                 [snippet12] -}
  h ⊤ = 0ℤ

module snippet13 {a b c d : Set} where
  {-                                                                 [snippet13] -}
  f : a → b
  g : c → b
  f = {!!}; g = {!!}
  {-                                                                 [snippet14] -}
  p : d → a
  q : d → c
  r : d → b
  p = {!!}; q = {!!}; r = {!!}
  {-
      a -- f --→ b ←-- g -- c  cospan: three objects (a, b, c) and two morphisms
                                       (f : a → b ← c : g)

                 D             cone: an apex (D) and three morphisms (p, r, q).
               / | \
              p  |  q
             /   |   \
            ↙    |    ↘
           a     r     c
            \    |    /
             f   |   g
              \  |  /
               ↘ ↓ ↙
                 b

  Commutativity conditions tell us that r is completely determined by the other
  morphisms, and can be omitted from the picture.  So we are only left with the
  following condition:                                               [snippet15] -}
  _ : g ∘ q ≡ f ∘ p
  _ = {!!}

{- A *pullback* is a universal cone of this shape.

                 D'
               / . \
              /  .  \
             /   .   \
            /    ↓    \
           /     D     \
          p'   /   \    q'
          |   p     q   |
          |  /       \  |
          ↓ ↙         ↘ ↓
           a           c
            \         /
             f       g
              \     /
               ↘   ↙
                 b

                                                                                 -}
module snippet16 {a : Set} where
  f : a → Float; f = {!!}
  {-                                                                 [snippet16] -}
  _ : ∃[ x ] f x ≡ 1.23
  _ = {!!}

{- 12.3 Colimits -----------------------------------------------------------------}

{- 12.4 Continuity ---------------------------------------------------------------}


module snippet17 {a b : Set} where
  record Contravariant (F : Set → Set) : Set₁ where
    constructor contravariant
    field contramap : (b → a) → (F a -> F b)

  open Contravariant ⦃...⦄

  {-                                                                 [snippet17] -}
  record ToString (a : Set) : Set where
    constructor toString
    field runToString : a → String
  instance
    tostring : Contravariant ToString
    tostring .contramap f (toString g) = toString (g ∘ f)
{-
ToString (Either b c) ~ (b → String, c → String)                     [snippet18] -}
{-                                                                   [snippet19] -}
{- r → a × b ~ (r → a , r → b)                                                   -}
