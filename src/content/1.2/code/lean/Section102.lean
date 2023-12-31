-- snippet 01
variable (x : Int)

-- snippet 02
namespace snippet02
  variable (f : Bool → Bool)
end snippet02

-- snippet 03
namespace snippet03
  def f : Bool → Bool := λ x => sorry
end snippet03

-- snippet 04
namespace snippet04
  def f : Bool → Bool := sorry
end snippet04

-- snippet 05
def fact (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (n + 1) * fact n

-- snippet 06
variable (a : Type)
variable (absurd : False → a)

-- snippet 07
def f44 : Empty → Int := λ _ => 44

-- snippet 08
def fInt : Int → Unit := λ x => ()

namespace snippet09
  def fInt : Int → Unit := λ _ => ()
end snippet09

-- snippet 10
def unit : a → Unit := λ _ => ()

namespace snippet11
  inductive Bool : Type where
    | true
    | false
end snippet11
