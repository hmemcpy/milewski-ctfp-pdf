(** Deriving typeclasses is not available as a language feature
    in OCaml. You could try ppxs to achieve similar results. *)
type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree
