(** OCaml doesn't have a built in Const type *)
type ('a, 'b) const = Const of 'a

type 'a option = ((unit, 'a) const, 'a id) Either.t
