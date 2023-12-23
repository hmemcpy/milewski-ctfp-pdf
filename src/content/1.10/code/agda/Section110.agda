{- Chapter 10. Natural Transformations -------------------------------------------}

module Section110 where

open import Agda.Builtin.Int using (Int; pos)
open import Data.Integer using (0ℤ; 1ℤ; _+_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Instances using ()
open import Data.Maybe using (Maybe)
open import Data.Maybe.Instances using ()
open import Data.Unit using (⊤; tt)
open import Effect.Functor using (RawFunctor)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open List
open Maybe
{-
      NATURAL TRANSFORMATIONS ARE MAPPINGS OF FUNCTORS
      THAT PRESERVE THEIR FUNCTORIAL NATURE.

A *natural transformation*, α : F ⇒ G, is a selection (or "family") of morphisms:
for each object a ∈ 𝒞ₒ, α picks one morphism from F a to G a. This morphism is
called the *component* of α at a (or "along" a) and is sometimes denoted αₐ.

                      α  : F ⇒ G
                    ----------------
                    αₐ : F a → G a
                    αᵤ : F u → G u
                    α̬  : F v → G v
                     ... etc ...

If there is an a ∈ 𝒞ₒ for which no morphism between F a and G a exists in 𝒟, then
there can be no natural transformation between F and G.

Consider a morphism f : u → v, (u, v ∈ 𝒞ₒ).  It's mapped to two morphisms, F f and
G f of 𝒟.
                 F f : F u → F v
                 G f : G u → G v

The natural transformation α : F ⇒ G provides two additional morphisms that
complete the diagram in 𝒟.

                αᵤ : F u → G u
                α̬ : F v → G v

                G ----→ G u
              /        ↗   \
            /         αᵤ     \
          /          /        G f
         u -- F → F u          \
         |           \          ↘
         |        . . \--------→ G v
         f      G      \        ↗
         |    .         F f    /
         |  .            \    α̬
         ↓.               ↘  /
         v ----- F -----→ F v

Now we have two ways of getting from F a to G b. To make sure that they are equal,
we must impose the *naturality condition* that holds for every f:

                G f ∘ αᵤ ≡ α̬  ∘ F f

The naturality condition is a pretty stringent requirement. For instance, if the
morphism F f is invertible, naturality determines α̬  in terms of αᵤ. It
*transports* αᵤ along f:

              α̬  ≡ G f ∘ αᵤ ∘ (F f)⁻¹
                                                                                 -}

{- 10.1 Polymorphic Functions ----------------------------------------------------}
private variable
  a b c e r : Set
  F G : Set → Set
  f : a → a

module snippet01 where
  α : ∀ a → F a → G a
  α = {!!}

module snippet02-03 where
  α : F a → G a
  α = {!!}

{-                                                                   [snippet04] -}
safeHead : List a → Maybe a
safeHead [] = nothing
safeHead (x ∷ xs) = just x

module snippet05 where
  open RawFunctor ⦃...⦄ renaming (_<$>_ to fmap)
  nc :  ∀{a : Set}{f : a → a}(l : List a)
    →   (fmap f ∘ safeHead) l ≡ (safeHead ∘ fmap f) l            -- [snippet05]  -}
  nc [] = refl
  nc (x ∷ l) = refl

module _ where
  open RawFunctor ⦃...⦄
  nc :  ∀{a : Set}{f : a → a}(l : List a)
    →   (f <$> safeHead l) ≡ safeHead (f <$> l)
  nc [] = refl
  nc (x ∷ l) = refl

{- We have two cases to consider; an empty list:
   fmap f (safeHead []) = fmap f nothing = nothing                   [snippet06]
   safeHead (fmap f []) = safeHead [] = nothing                      [snippet07]
and a non-empty list:
   fmap f (safeHead (x ∷ xs)) = fmap f (just x) = just (f x)         [snippet08]
   safeHead (fmap f (x ∷ xs)) = safeHead (f x ∷ fmap f xs) = just (f x)
                                                                     [snippet09]
                                                                     [snippet10] -}
module snippet10 where
  fmap : (a → b) → List a → List b
  fmap f [] = []
  fmap f (x ∷ xs) = f x ∷ fmap f xs

{-                                                                   [snippet11] -}
module snippet11 where
  fmap : (a → b) → Maybe a → Maybe b
  fmap f nothing = nothing
  fmap f (just x) = just (f x)

record Functor (F : Set → Set) : Set₁ where
  constructor functor
  field fmap : (a → b) → F a → F b
open Functor ⦃...⦄

module snippet12 where
  data Const (c a : Set) : Set where
    const : c → Const c a
  {-                                                                 [snippet13] -}
  unConst : Const c a → c
  unConst (const c) = c

  instance
    constFunctor : Functor (Const c)
    constFunctor .fmap = λ f → λ where (const c) → const c
  {-                                                                 [snippet12] -}
  length : List a → Const Int a
  length [] = const 0ℤ
  length (x ∷ xs) = const (1ℤ + unConst (length xs))

  {- length : List a → Int                                           [snippet14] -}
  {-                                                                 [snippet15] -}
  scam : Const Int a → Maybe a
  scam (const x) = nothing

module Reader where
  {-                                                                 [snippet16] -}
  record Reader (e : Set) (a : Set) : Set where
    constructor reader
    field runReader : e → a
  {-                                                                 [snippet17] -}
  instance
    readerFunctor : Functor (Reader e)
    readerFunctor .fmap f (reader g) = reader (f ∘ g)
  {- (Recall, Functor (Reader e) is (a → b) → Reader e a → Reader e b.) -}

  instance
    readerUnitFunctor : Functor (Reader ⊤)
    readerUnitFunctor .fmap f (reader g) = reader (f ∘ g)
  {-                                                                 [snippet18] -}
  α : Reader ⊤ a → Maybe a
  {- α (reader _) = nothing                                          [snippet19]
                                                                     [snippet20] -}
  α (reader g) = just (g tt)

{- 10.2 Beyond Naturality --------------------------------------------------------}
record Contravariant (F : Set → Set) : Set₁ where
  constructor contravariant
  field contramap : (b → a) → (F a -> F b)
open Contravariant ⦃...⦄

module Op where
  {-                                                                 [snippet21] -}
  record Op (r : Set)(a : Set) : Set where
    constructor op
    field runOp : a → r
  {-                                                                 [snippet22] -}
  instance
    opContra : Contravariant (Op r)
    opContra .contramap f (op g) = op (g ∘ f)
  {- Contravariant (Op r) is (b → a) → (Op r a → Op r b).                        -}
  predToStr : Op Bool a → Op String a
  {-                                                                 [snippet23] -}
  predToStr (op f) = op λ x → if (f x) then "T" else "F"
  {-                                                                 [snippet24] -}
  _ : {f : b → a} → contramap f ∘ predToStr ≡ predToStr ∘ (contramap f)
  _ = refl

{- 10.3 Functor Category ---------------------------------------------------------}
{-                  βᵤ ∘ αᵤ : F a → H a.
                    (β ∘ α)ᵤ = βᵤ ∘ αᵤ.

             F u ____
            ↗  \     \
           /    αᵤ     \
          F      \      \
         /        ↘      \
        u ------→ G u  (β ∘ α)ᵤ
         \        ↗      /
          H      /      /
           \    βᵤ     /
            ↘  /     /
            H u ←----
                                                                                 -}

{- 10.4 2-Categories -------------------------------------------------------------}
{- 10.5 Conclusion ---------------------------------------------------------------}

