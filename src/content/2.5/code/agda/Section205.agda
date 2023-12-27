{-- 15 The Yoneda Lemma ----------------------------------------------------------}

module Section205 where

-- open import Agda.Builtin.Nat using (_+_; _-_; _==_)
-- open import Data.Bool.Base using (if_then_else_)
-- open import Data.Integer using (ℤ; +_)
-- open import Data.List using (List; map; [_])
-- open import Data.Nat using (ℕ)
open import Function using (_∘_; id)
-- open import Relation.Binary.PropositionalEquality using (_≡_; refl)
private variable a : Set -- b c d x y : Set

{- Main points from intro:
   - Setting: an arbitrary category ℂ together with a functor F from ℂ to 𝕊𝕖𝕥.
   - Some 𝕊𝕖𝕥-valued functors are *representable* (isomorphic to a hom-functor).

   - YONEDA LEMMA: all 𝕊𝕖𝕥-valued functors can be obtained from hom-functors via
     nat transfs, and the Yoneda Lemma enumerates all such transformations.

     Yoneda tells us that a nat transf α between a hom-functor and another functor
     is completely determined by specifying the value of α's component at just one
     point.  The rest of α is given by the naturality condition.

   - NATURALITY CONDITION:

     - hom-functor:                   x ↦ ℂ(a, x); f ↦ ℂ(a, f),
     - arbitrary 𝕊𝕖𝕥-valued functor:  F : ℂ → 𝕊𝕖𝕥:
     - natural transformation:        α : ℂ(a, -) ⇒ F, a
     - naturality condition:          α(y) ∘ ℂ(a, f) = F f ∘ α(x)

   - Components of α are functions between sets: ∀ x . α(x) : ℂ(a, x) → F x

           ℂ(a, x) ---------------→ ℂ(a, y)
              |         ℂ(a, f)        |
              |                        |
          α(x)|                        | α(y)
              |                        |
              |                        |
              ↓                        ↓
              F x ------------------→ F y
                          F f

   - NATURALITY SQUARE FOR α: pointwise, at h ∈ ℂ(a, x),

            α(y) (ℂ(a, f) h) = (F f) (α(x) h)               (*)

   - ACTION OF HOM-FUNCTOR: ℂ(a, -): ℂ(x, y) → ℂ(a, x) → ℂ(a, y)

     ... is precomposition: ℂ(a, f): ℂ(a, x) → ℂ(a, y); h ↦ f ∘ h

            α(y) (f ∘ h) = (F f) (α(x) h)                   (⋆)

   - Specializing to case x = a: h ∈ ℂ(a, a), eg, h = idₐ. Plug it in:

                  α(y) f = (F f) (α(a) idₐ)

     The lhs is the action of α(y) on an arbitrary f ∈ ℂ(a, y).
     It is determined by the single value (α(a) idₐ) ∈ F a.  Any such value
     generates the natural transformation α.

   - Conversely, given any nat transf α : ℂ(a, -) ⇒ F, evaluating α(a) at idₐ to
     get an ("α-defining") point α(a) idₐ ∈ F a.

   - YONEDA LEMMA:  ℕ𝕒𝕥(ℂ(a, -), F) ≅ F a

     In the notation [ℂ, 𝕊𝕖𝕥] for the functor category between ℂ and 𝕊𝕖𝕥,
     the set of nat transfs is just a hom-set in that category, and we can write:

                   [ℂ, 𝕊𝕖𝕥](ℂ(a, -), F) ≅ F a

     This correspondence is in fact a *natural isomorphism*.

   - Consider the image of ℂ under ℂ(a, -).  Start with the image of under
     ℂ(a, -): a ↦ ℂ(a, a).  Under F: a ↦ F a.  The component α(a) is some function
     from ℂ(a, a) to F a.  Let p ∈ ℂ(a, a) be the point idₐ.  α(a): p ↦ q, for some
     q ∈ F a.  ANY CHOICE OF q LEADS TO A UNIQUE α.

                                ℂ(a, a)

                                  p
                                ↗ |
                         ℂ(a,-)/  |
                              /   |
                            a     |α(a)
                              \   |
                             F \  |
                                ↘ ↓
                                  q

                                 F a

   - FIRST CLAIM: the choice of q uniquely determines the rest of α(a).

     Here's the magic of Yoneda: consider any other point g ∈ ℂ(a, a) under the
     hom-functor: g ↦ ℂ(a, g); under F : g ↦ F g.

     The action of ℂ(a, g) on p = idₐ is the precomposition g ∘ idₐ = g, so g maps
     to a function that maps idₐ to g.

     The action of F g on q is some q' ∈ F a.  To complete the naturality
     square, g is mapped to q' under α(a).  We picked an arbitrary g and derived
     its mapping under α(a).  The function α(a) is thus completely determined.

   - SECOND CLAIM: ∀ x ∈ ℂ, α(x) is uniquely determined.

     Case 1. ℂ(a, x) ≠ ∅

       Pick an arbitrary g ∈ ℂ(a, x).
       Under ℂ(a, -): g ↦ ℂ(a, g)  : ℂ(a, a) → ℂ(a, x)
       Under F:       g ↦ F g      : F a → F x
       ℂ(a, g): idₐ ↦ g ∘ idₐ = g.
       Naturality implies α(x) g = (F g) q, where q was chosen above.  Since g was
       arbitrary, the whole function α(x) is thus determined.

                                ℂ(a, a)          ℂ(a, x)

                                 p ---------------→ g
                               ↗  |     ℂ(a, g)     |
                       ℂ(a, -)/   |                 |
                             /    |                 |
                            a     |α(a)             |α(x)
                           / \    |                 |
                          /  F\   |                 |
                         /     ↘  ↓        F g      ↓
                         |       q ---------------→ q'
                          \     F a                F x
                           ↘                      ↗
                             x __________________/
                                      F

     Case 2. ℂ(a, x) = ∅

       Recall ∅ is the initial object in 𝕊𝕖𝕥 (∃! map from ∅ to any other set); we
       called the unique map from ∅ to any other set `absurd`.  Thus, when
       ℂ(a, x) = ∅, `absurd` is the only choice for the component α(x).          -}

{- 15.1 Yoneda in Haskell --------------------------------------------------------}
{-                                                                   [snippet01] -}
data Reader a x : Set where
  reader : (a → x) → Reader a x

record Functor (F : Set → Set) : Set₁ where
  field fmap : {x y : Set} → (x → y) → F x → F y
open Functor ⦃...⦄

module snippet02 where
  instance
    readerFunctor : Functor (Reader a)
    readerFunctor .fmap f (reader g) = reader (f ∘ g)

module snippet03 {F : Set → Set} where
  {-                                                                 [snippet04] -}
  α : ∀ x → (a → x) → F x
  α = {!!}

  module snippet05 {a : Set} where
    _ : F a
    _ = α(a) id

module snippet06 {a : Set} where
  F : Set → Set
  F = Reader a
  {-                                                                 [snippet06] -}
  fa : F a
  fa = {!!}
  α : ∀{x} → (a → x) → F x
  {-                                                                 [snippet07] -}
  α h = fmap h fa

{- 15.2 Co-Yoneda ----------------------------------------------------------------}

