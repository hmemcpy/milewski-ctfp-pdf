{- Chapter 6. Simple Algebraic Data Types ----------------------------------------}

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

{- Section 6.1. Product Types ----------------------------------------------------}
{-                                                                   [snippet01] -}
swap : (a × b) → (b × a)
swap (x , y) = y , x

{-
 (a × b) × c                                                         [snippet02]
 a × b × c                                                           [snippet03]
                                                                     [snippet04] -}
alpha : (a × b) × c → a × b × c
alpha ((x , y) , z) = x , y , z
{-                                                                   [snippet05] -}
alpha-inv : a × b × c → (a × b) × c
alpha-inv (x , y , z) = (x , y) , z
{-
 a × ⊤                                                               [snippet06]
                                                                     [snippet07] -}
rho : a × ⊤ → a
rho (x , tt) = x
{-                                                                   [snippet08] -}

rho-inv : a → a × ⊤
rho-inv x = x , tt

module snippet9 where
  open import Data.Bool using (Bool; false; true; _∧_)
  data Pair (a b : Set) : Set where
    P : a → b → Pair a b

{-                                                                   [snippet10] -}
  stmt : Pair String Bool
  stmt = P "This statement is" false

{-                                                                   [snippet11] -}
data Pair (a b : Set) : Set where
  pair : a → b → Pair a b

module snippet12 where
  open import Data.Bool using (Bool; false)
  stmt : String × Bool
  stmt = _,_ "This statement is" false

module snippet13 where
  open import Data.Bool using (Bool)
  data Stmt : Set where
    stmt : String → Bool → Stmt

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

{-                                                                   [snippet15] -}
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
  startsWithSymbol : Element → Bool
  startsWithSymbol e = symbol e isPrefixOf name e

{- Section 6.3. Sum Types --------------------------------------------------------}
{-                                                                   [snippet21] -}
data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b
{-                                                                   [snippet22] -}
data OneOfThree (a b c : Set) : Set where
  Sinistral : a → OneOfThree a b c
  Medial    : b → OneOfThree a b c
  Dextral   : c → OneOfThree a b c
{-                                                                   [snippet23] -}
_ : Either a ⊥
_ = {!   !}
{-                                                                   [snippet24] -}
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

{-                                                                   [snippet27] -}
data NothingType : Set where
  Nothing : NothingType
{-                                                                   [snippet28] -}
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
{-                                                                   [snippet32] -}
snippet32 : a × Either b c
snippet32 = {!   !}
{-                                                                   [snippet33] -}
snippet33 : Either (a × b) (a × c)
snippet33 = {!   !}
{-                                                                   [snippet34] -}
prodToSum : a × Either b c → Either (a × b) (a × c)
prodToSum (x , Left y)  = Left (x , y)
prodToSum (x , Right z) = Right (x , z)
{-                                                                   [snippet35] -}
sumToProd : Either (a × b) (a × c) → a × Either b c
sumToProd e = case e of λ where
  (Left  (x , y)) → x , Left  y
  (Right (x , z)) → x , Right z
{- alternatively -}
sumToProd' : Either (a × b) (a × c) → a × Either b c
sumToProd' (Left (x , y))  = x , Left y
sumToProd' (Right (x , z)) = x , Right z
{-                                                                   [snippet36] -}
prod1 : ℤ × Either String Float
prod1 = ℤ.pos 2 , Left "Hi!"
{-                                                                   [snippet37] -}
data List (a : Set) : Set where
  Nil : List a
  Cons : a → List a → List a

