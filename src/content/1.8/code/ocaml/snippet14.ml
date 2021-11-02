(** Deriving a functor in OCaml is not available as a language
    extension. You could try experimental library like ocsigen
    to derive functors.*)
type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree
