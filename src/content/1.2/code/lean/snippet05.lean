def fact (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (n + 1) * fact n
