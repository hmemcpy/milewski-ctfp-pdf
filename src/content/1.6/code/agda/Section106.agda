{- Chapter 6. Simple Algebraic Data Types ----------------------------------------}
{- We've seen two basic ways of combining types: using a product and a coproduct.
It turns out that a lot of data structures in everyday programming can be built
using just these two mechanisms.  This fact has important practical consequences.
Many properties of data structures are composable.  For instance, if you know how
to compare values of basic types for equality, and you know how to generalize
these comparisons to product and coproduct types, you can automate the derivation
of equality operators for composite types.  In Haskell you can automatically
derive equality, comparison, conversion to and from string, and more, for a large
subset of composite types.

Let's have a closer look at product and sum types as they appear in
programming.                                                                     -}

{- Section 6.1. Product Types ----------------------------------------------------}
{- The canonical implementation of a product of two types in a programming
language is a pair.  In Haskell, a pair is a primitive type constructor; in C++
it's a relatively complex template defined in the Standard Library.              -}

module Section106 where

open import Data.Char
open import Data.Empty using (⊥)
open import Data.Float using (Float)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_)

variable a b c : Set

{- Pairs are not strictly commutative: a pair in Int × Bool cannot be substituted
for a pair Bool × Int, even though they carry the same information.  They are,
however, commutative up to isomorphism---the isomorphism being given by the swap
function (which is its own inverse, hence a so called "involution"):
                                                                     [snippet01] -}
swap : (a × b) → (b × a)
swap (x , y) = y , x

{- You can think of the two pairs as simply using a different format for storing
the same data.  It's just like big endian vs. little endian.  You can combine an
arbitrary number of types into a product by nesting pairs inside pairs, but there
is an easier way: nested pairs are equivalent to tuples.  It's a consequence of
the fact that different ways of nesting pairs are isomorphic.  If you want to
combine three types, a, b, c, in a product, in that order, you can do it in two
ways:

(a × b) × c                                                          [snippet02]

Or:

a × b × c                                                            [snippet03]

These types are different---you can't pass one to a function that expects the
other---but their elements are in one-to-one correspondence.  There is a function
that maps one to the other:                                          [snippet04] -}

alpha : (a × b) × c → a × b × c
alpha ((x , y) , z) = x , y , z

{- and this function is invertible:                                  [snippet05] -}
alpha-inv : a × b × c → (a × b) × c
alpha-inv (x , y , z) = (x , y) , z

{- so it's an isomorphism.  These are just different ways of repackaging the
same data. -}

{- If we can live with isomorphisms, and don't insist on strict equality, then we
can even show that the unit type, ⊤ , is the unit of the product the same way 1 is
the unit of multiplication.  Indeed, the pairing of a value of some type a with a
unit doesn't add any information.  The type

                 a × ⊤                                               [snippet06]

is isomorphic to a.  Here's the isomorphism:                         [snippet07] -}
rho : a × ⊤ → a
rho (x , tt) = x

{- and its inverse:                                                  [snippet08] -}

rho-inv : a → a × ⊤
rho-inv x = x , tt

{- These observations can be formalized by saying that 𝕊𝕖𝕥 (the category of sets)
is a *monoidal category*.  It's a category that's also a monoid, in the sense that
you can multiply objects (here, take their Cartesian product) and there's a
multiplicative identity (here, ⊤).  We'll talk more about monoidal categories, and
give the full definition later.

There is a more general way of defining product types in Haskell, especially when
they are combined with sum types.  It uses named constructors with multiple
arguments. A pair, for instance, can be defined alternatively as:                -}
module snippet9 where
  open import Data.Bool using (Bool; false; true; _∧_)
{-                                                                   [snippet09] -}
  data Pair (a b : Set) : Set where
    P : a → b → Pair a b

{- Here, Pair a b is the name of the type parameterized by two other types, a b;
P is the name of the data constructor.  You define a pair *type* by passing two
types to the type constructor Pair.  You construct a pair value by passing two
values of the appropriate types to the data constructor P.  For instance, let's
define a value stmt as a pair of String and Bool:                    [snippet10] -}

  stmt : Pair String Bool
  stmt = P "This statement is" false

{- The first line is the type declaration.  It uses the type constructor Pair,
with String and Bool replacing the a and b in the generic definition of Pair.  The
second line defines the actual value by passing a concrete string and a concrete
Boolean to the data constructor P.  Type constructors are used to construct types;
data constructors, to construct values.

Since the name spaces for type and data constructors are separate in
Haskell, you will often see the same name used for both.  However, in Agda this is
not so and we must use a different name for the data constructor, as in:
                                                                     [snippet11] -}
data Pair (a b : Set) : Set where
  pair : a → b → Pair a b

{- If you squint hard enough, you may even view the built-in product type as a
variation on this kind of declaration, where the name Pair is replaced with the
binary operator _×_ and the constructor pair is replaced with _,_.  In fact you
can use _,_ just like any other named constructor and create pairs using prefix
notation:                                                            [snippet12] -}
module snippet12 where
  open import Data.Bool using (Bool; false)
  stmt : String × Bool
  stmt = _,_ "This statement is" false

{- Actually, Agda's built-in product type is not defined as an inductive
  data type, but rather as a special case of the dependent pair type; the latter
  is defined as a record type:
  record type record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      fst : A
      snd : B fst                                                                -}

{- Similarly, you can use _,_,_ to create triples, and so on.  But instead of
using generic pairs or tuples, you could define specific named product types, as
in:                                                                              -}
module snippet13 where
  open import Data.Bool using (Bool)
  {-                                                                 [snippet13] -}
  data Stmt : Set where
    stmt : String → Bool → Stmt
  {- which is just a product of String and Bool, but it's given its own name and
  constructor. The advantage of this style of declaration is that you may define
  many types that have the same content but different meaning and functionality,
  and which cannot be substituted for each other.                                -}

{- Section 6.2. Records ----------------------------------------------------------}
module snippet14 where
  open import Data.Bool using (Bool; true; false; _∧_)
  open import Data.List
  isPrefixOf : String → String → Bool
  isPrefixOf s s' = isPrefix-Chars (toList s) (toList s')
    where
    isPrefix-Chars : List Char → List Char → Bool
    isPrefix-Chars _ [] = true
    isPrefix-Chars [] _ = false
    isPrefix-Chars (x ∷ xs) (y ∷ ys) = (x ≈ᵇ y) ∧ isPrefix-Chars xs ys

  startsWithSymbol : String × String × ℤ → Bool
  startsWithSymbol (name , symbol , _) = isPrefixOf symbol name

{- This code is error prone, and is hard to read and maintain. It's much
better to define a record:                                           [snippet15] -}
record Element : Set where
  constructor element
  field
    name          : String
    symbol        : String
    atomicNumber  : ℤ
open Element
{-                                                                   [snippet16] -}
tupleToElem : String × String × ℤ → Element
tupleToElem (n , s , a) = element s s a
{-                                                                   [snippet17] -}
elemToTuple : Element → String × String × ℤ
elemToTuple e = name e , name e , atomicNumber e
{-                                                                   [snippet18] -}
AtomicNumber : Element → ℤ
AtomicNumber = atomicNumber

module snippet19 where
  open import Data.Bool using (Bool; true; false; _∧_)
  open import Data.List
  isPrefixOf : String → String → Bool
  isPrefixOf s s' = isPrefix-Chars (toList s) (toList s')
    where
    isPrefix-Chars : List Char → List Char → Bool
    isPrefix-Chars _ [] = true
    isPrefix-Chars [] _ = false
    isPrefix-Chars (x ∷ xs) (y ∷ ys) = (x ≈ᵇ y) ∧ isPrefix-Chars xs ys
  {-                                                                 [snippet19] -}
  startsWithSymbol : Element → Bool
  startsWithSymbol e = isPrefixOf (symbol e) (name e)

module snippet20 where
  open import Data.Bool using (Bool; true; false; _∧_)
  open import Data.List
  _isPrefixOf_ : String → String → Bool
  s isPrefixOf s' = isPrefix-Chars (toList s) (toList s')
    where
    isPrefix-Chars : List Char → List Char → Bool
    isPrefix-Chars _ [] = true
    isPrefix-Chars [] _ = false
    isPrefix-Chars (x ∷ xs) (y ∷ ys) = (x ≈ᵇ y) ∧ isPrefix-Chars xs ys
  {-                                                                 [snippet19] -}
  startsWithSymbol : Element → Bool
  startsWithSymbol e = symbol e isPrefixOf name e
  {- The parentheses can be omitted since an infix operator has lower precedence
  than a function call.                                                          -}

{- Section 6.3. Sum Types --------------------------------------------------------}
{- Just as the product in the category of sets gives rise to product types, the
coproduct gives rise to sum types.  The canonical implementation of a sum type in
Agda is:                                                             [snippet21] -}
data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b
{- And like pairs, Eithers are commutative (up to isomorphism), can be nested, and
the nesting order is irrelevant (up to isomorphism).  So we can, for instance,
define a sum equivalent of a triple:                                 [snippet22] -}
data OneOfThree (a b c : Set) : Set where
  Sinistral : a → OneOfThree a b c
  Medial    : b → OneOfThree a b c
  Dextral   : c → OneOfThree a b c
{- It turns out that 𝕊𝕖𝕥 is also a (symmetric) monoidal category with respect to
coproduct.  The role of the binary operation is played by the disjoint sum, and
the role of the unit element is played by the initial object.  In terms of types,
we have Either as the monoidal operator and ⊥, the uninhabited type, as its
neutral element.  You can think of Either as plus, and ⊥ as zero.  Indeed, adding
⊥ to a sum type doesn't change its content. For instance:            [snippet23] -}
_ : Either a ⊥
_ = {!   !}
{- is isomorphic to a.  That's because there is no way to construct a Right
version of this type---there isn't a value of type ⊥.  The only inhabitants of
Either a ⊥ are constructed using the Left constructors and they simply encapsulate
a value of type a.  So, symbolically, a + 0 = a.
                                                                     [snippet24] -}
data Color : Set where
  Red   : Color
  Green : Color
  Blue  : Color
{-                                                                   [snippet25] -}
module snippet25 where
  data Bool : Set where
    True False : Bool
{-                                                                   [snippet26] -}
module snippet26 where
  data Maybe (a : Set) : Set where
    Nothing : Maybe a
    Just    : a → Maybe a

{- The Maybe type is a sum of two types.  You can see this if you separate the two
constructors into individual types.  The first one would look like this:
                                                                     [snippet27] -}
data NothingType : Set where
  Nothing : NothingType
{- It's an enumeration with one value called Nothing.  In other words, it's a
singleton, which is equivalent to the unit type ⊤.  The second part: [snippet28] -}
data JustType (a : Set) : Set where
  Just : a → JustType a
{-                                                                   [snippet29] -}
module snippet29 where
  Maybe : Set₁
  Maybe = ∀ (a : Set) → Either ⊤ a
{-                                                                   [snippet30] -}
module snippet30 where
  data List (a : Set) : Set where
    Nil  : List a
    Cons : a → List a → List a

  open import snippet26
  {-                                                                 [snippet31] -}
  maybeTail : List a → Maybe (List a)
  maybeTail Nil = Nothing
  maybeTail (Cons _ t) = Just t

{- Section 6.4. Algebra of Types -------------------------------------------------}
{- We've seen two commutative monoidal structures underlying the type system: We
have the sum types with ⊥ as the neutral element, and the product types with the
unit type, ⊤, as the neutral element.  We'd like to think of them as analogous to
addition and multiplication.  In this analogy, ⊥ would correspond to zero, and ⊤
to one.

Let's see how far we can stretch this analogy.  For instance, does multiplication
by zero give zero?  In other words, is a product type with one component being
⊥ isomorphic to ⊥?  For example, is it possible to create a pair of, say ℤ and ⊥?

To create a pair you need two values.  Although you can easily come up with an
integer, there is no value of type ⊥.  Therefore, for any type a, the type
a × ⊥ is uninhabited and is therefore equivalent to ⊥.  In other words, a × 0 = 0.

Another thing that links addition and multiplication is the distributive property:

               a × (b + c) ≡ a × b + a × c

Does it also hold for product and sum types?  Yes, it does---up to isomorphisms,
as usual.  The left-hand side corresponds to the type:               [snippet32] -}
snippet32 : a × Either b c
snippet32 = {!   !}
{- and the right hand side corresponds to the type:                  [snippet33] -}
snippet33 : Either (a × b) (a × c)
snippet33 = {!   !}
{- Here's the function that converts them one way:                   [snippet34] -}
prodToSum : a × Either b c → Either (a × b) (a × c)
prodToSum (x , Left y)  = Left (x , y)
prodToSum (x , Right z) = Right (x , z)
{- and here's one that goes the other way:                           [snippet35] -}
sumToProd : Either (a × b) (a × c) → a × Either b c
sumToProd e = case e of λ where
  (Left  (x , y)) → x , Left  y
  (Right (x , z)) → x , Right z
{- alternatively -}
sumToProd' : Either (a × b) (a × c) → a × Either b c
sumToProd' (Left (x , y))  = x , Left y
sumToProd' (Right (x , z)) = x , Right z
{- The case_of_ statement is used for pattern matching inside functions.  Each
pattern is followed by an arrow and the expression to be evaluated when the
pattern matches.  For instance, if you call prodToSum with the value:
                                                                     [snippet36] -}
prod1 : ℤ × Either String Float
prod1 = ℤ.pos 2 , Left "Hi!"
{- then the e in `case e of` will be equal to Left "Hi!".  It will match the
pattern Left y, substituting "Hi!" for y.  Since the x  has already been matched
to 2, the result of the case_of_ clause, and the whole function, will be
Left (2, "Hi!"), as expected.

Such intertwined monoids are called *semirings*.  These are not full rings because
we can't define subtraction of types.  That's why a semiring is sometimes called a
*rig*---a "ring without an n" (negative).  Barring that, we can get a lot of
mileage from translating statements about, say, natural numbers, which form a rig,
to statements about types.                                          [snippet37] -}
data List (a : Set) : Set where
  Nil : List a
  Cons : a → List a → List a

{- Section 6.5. Challenges -------------------------------------------------------}

{- 1. Show the isomorphism between Maybe a and Either ⊤ a.                       -}

{- 2. Here's a sum type defined in Haskell:

      data Shape =  Circle Float
                  | Rect Float Float

      When we want to define a function like area that acts on a Shape, we do it
      by pattern matching on the two constructors:

      area :: Shape -> Float
      area (Circle r) = pi * r * r
      area (Rect d h) = d * h

      Implement Shape in C++ or Java as an interface and create two classes:
      Circle and Rect.  Implement area as a virtual function.                    -}
{- 3. Continuing with the previous example: We can easily add a new function circ
      that calculates the circumference of a Shape.  We can do it without touching
      the definition of Shape:

      circ :: Shape -> Float
      circ (Circle r) = 2.0 * pi * r
      circ (Rect d h) = 2.0 * (d + h)

      Add circ to your C++ or Java implementation.  What parts of the original
      code did you have to touch?                                                -}

{- 4. Continuing further: Add a new shape, Square, to Shape and make all the
      necessary updates.  What code did you have to touch in Haskell vs. C++ or
      Java?  (Even if you're not a Haskell programmer, the modifications should be
      pretty obvious.)                                                           -}
{- 5. Show that a + a = 2 × a holds for types (up to isomorphism).  Remember that
      2 corresponds to Bool, according to our translation table.                 -}
