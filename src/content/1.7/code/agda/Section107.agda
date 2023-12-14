{- 7 Functors -----------------------------------------------------------}
{- A functor is a mapping between categories.  Given two categories, ℂ and 𝔻, a
functor F maps objects in ℂ to objects in 𝔻---it's a function on objects.  If a is
an object in ℂ, we'll write its image in 𝔻 as F a (no parentheses).  But a
category is not just objects---it's objects and morphisms that connect them.  A
functor also maps morphisms---it's a function on morphisms.  But it doesn't map
morphisms willy-nilly---it preserves connections.  So if a morphism f in ℂ
connects object a to object b, f : a → b, then the image of f in 𝔻, F f, will
connect the image of a to the image of b: F f : F a → F b.

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
{- Let's get down to earth and talk about programming.  We have our category of
types and functions.  We can talk about functors that map this category into
itself---such functors are called endofunctors.  So what's an endofunctor in the
category of types?  First of all, it maps types to types.  We've seen examples of
such mappings, maybe without realizing that they were just that.  I'm talking about
definitions of types that were parameterized by other types. Let's see a few
examples.                                                                        -}
{- 7.1.1 The Maybe Functor -------------------------------------------------------}
{- The definition of Maybe is a mapping from types to types that takes a given
type a to type Maybe a:                                              [snippet01] -}
data Maybe (a : Set) : Set where
  Nothing : Maybe a
  Just : a → Maybe a
{- Here's an important subtlety: Maybe itself is not a type, it's a *type
constructor*.  You have to give it a type argument, like Int or Bool, in order to
turn it into a type.  Maybe without any argument represents a function on types.
But can we turn Maybe into a functor?  (From now on, when we speak of functors in
the context of programming, we almost always mean endofunctors.)  A functor is not
only a mapping of objects (here, types) but also a mapping of morphisms (here,
functions). For any function from a to b:                            [snippet02] -}
f : a → b
f = {!!}
{- we would like to produce a function from Maybe a to Maybe b.  To define such a
function, we'll have two cases to consider, corresponding to the two constructors
of Maybe.  The Nothing case is simple: just return Nothing.  If the argument is
Just x, then we'll apply the function, f, to the contents, x, of Just.  So the
image of f under Maybe is the function:                              [snippet03] -}
f' : Maybe a → Maybe b
f' Nothing = Nothing
f' (Just x) = Just (f x)

{- We implement the morphism-mapping part of a functor as a higher order function
called fmap.  In the case of Maybe, it has the following signature and definition:
                                                                                 -}
module snippet04 where
  fmap : (a → b) → Maybe a → Maybe b                              -- [snippet05] -}
  fmap _ Nothing = Nothing                                        -- [snippet06] -}
  fmap f (Just x) = Just (f x)

{- 7.1.2 Equational Reasoning ----------------------------------------------------}

{-                                                                   [snippet07] -}
id : a → a
id x = x

{- If a function is defined by pattern matching, you can use each sub-definition
independently.  For instance, given the above definition of fmap you can replace
fmap f Nothing with Nothing, or the other way around.  Let's see how this works in
practice.  Let's start with the preservation of identity:                        -}
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
{- A typeclass defines a family of types that support a common interface. For
instance, the class of objects that support equality is defined as follows:
                                                                     [snippet10] -}
record Eq (a : Set) : Set where
  field _==_ : a → a → Bool

open Eq ⦃...⦄

{- This definition states that type a is of the class Eq if it supports the
operator (==) that takes two arguments of type a and returns a Bool. If you want
to tell Agda that a particular type has such an equality, you have to declare it
an instance of this type class and provide the implementation of (==). For
example, given the definition of a 2D Point (a product type of two Floats),
                                                                     [snippet11] -}
data Point : Set where
  Pt : Float → Float → Point
{- we can define the equality of points:                             [snippet12] -}
instance
  floatEq : Eq Float
  floatEq ._==_ = λ x y → does (x ≟ y)

  pointEq : Eq Point
  pointEq ._==_ = eq
    where
    eq : Point → Point → Bool
    eq (Pt x₁ y₁) (Pt x₂ y₂) = x₁ == x₂ ∧ y₁ == y₂

{- Typeclasses are also Haskell's only mechanism for overloading functions (and
operators).  We will need that for overloading fmap for different functors.  There
is one complication, though: a functor is not defined as a type but as a mapping
of types, a type constructor.  We need a typeclass that's not a family of types,
as was the case with Eq, but a family of type constructors.  Fortunately a Haskell
typeclass works with type constructors as well as with types.  So here's the
definition of the Functor class:                                     [snippet13] -}
record Functor (f : Set → Set) : Set₁ where
  field fmap : (a → b) → f a → f b
{- (We use lower case f, a, b here for consistency with the text, though we would
prefer to use capital F for the type constructor/functor and capital letters like
a and b for types.)

The above record definition stipulates that f is a Functor if there exists a
function fmap with the specified type signature.  The lowercase f is a type
variable, similar to type variables a and b.  The compiler, however, is able to
deduce that it represents a type constructor rather than a type by looking at its
usage: acting on other types, as in f a and f b. Accordingly, when declaring an
instance of Functor, you have to give it a type constructor, as is the case with
Maybe:                                                               [snippet14] -}
open Functor ⦃...⦄
instance
  maybeFunctor : Functor Maybe
  maybeFunctor .fmap = λ f → λ where
    Nothing → Nothing
    (Just a) → Just (f a)

{- 7.1.6 The List Functor --------------------------------------------------------}
{- To get some intuition for the role of functors in programming, we need to look
at more examples.  Any type that is parameterized by another type is a candidate
for a functor.  Generic containers are parameterized by the type of the elements
they store, so let's look at a very simple container, the list:      [snippet15] -}
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
{- We've seen some examples of functors in programming languages that define
general-purpose containers, or at least objects that contain some value of the
type they are parameterized over.  The reader functor seems to be an outlier,
because we don't think of functions as data.  But we've seen that pure functions
can be memoized, and function execution can be turned into table lookup.  Tables
are data.  Conversely, because of Haskell's laziness, a traditional container,
like a list, may actually be implemented as a function.  Consider, for instance,
an infinite list of natural numbers, which can be compactly defined as:          -}
{-                                                                   [snippet25] -}
nats : Stream ℕ ∞
nats = iterate suc zero
{- Obviously, an infinite list like this cannot be stored in memory.  The compiler
implements it as a function that generates nats on demand.  This effectively blurs
the distinction between data and code.  A list could be considered a function, and
a function could be considered a table that maps arguments to results.  The latter
can even be practical if the domain of the function is finite and not too large.
It would not be practical, however, to implement strlen as table lookup, because
there are infinitely many different strings.  As programmers, we don't like
infinities, but in category theory you learn to eat infinities for breakfast.
Whether it's a set of all strings or a collection of all possible states of the
Universe, past, present, and future---we can deal with it!  So I like to think of
the functor object (an object of the type generated by an endofunctor) as
containing a value or values of the type over which it is parameterized, even if
these values are not physically present there.  One example of a functor is a
Haskell IO object, which may contain user input, or the future versions of our
Universe with "Hello World!" displayed on the monitor.  According to this
interpretation, a functor object is something that may contain a value or values
of the type it's parameterized upon.  Or it may contain a recipe for generating
those values.  We are not at all concerned about being able to access the
values---that's totally optional, and outside of the scope of the functor.  All we
are interested in is our ability to manipulate those values using functions.  If
the values can be accessed, then we should be able to see the results of this
manipulation.  If they can't, then all we care about is that the manipulations
compose correctly and that the manipulation with an identity function doesn't
change anything.  Just to show you how much we don't care about being able to
access the values inside a functor object, here's a type constructor that ignores
completely its argument a:                                           [snippet26] -}
data Const (c a : Set) : Set where
  mkConst : c → Const c a
{- The Const type constructor takes two types, c and a.  Just like we did with the
arrow constructor, we are going to partially apply it to create a functor.  The
data constructor (called mkConst) takes just one value of type c.  It has no
dependence on a.  The type of fmap for this type constructor is:
  fmap : (a → b) → Const c a → Const c b                            [snippet27] -}
{- Because the functor ignores its type argument, the implementation of fmap is
free to ignore its function argument---the function has nothing to act upon:
                                                                     [snippet28] -}
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
