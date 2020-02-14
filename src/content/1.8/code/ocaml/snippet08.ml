(** OCaml doesn't have a built in Const type *)
type ('a, 'b) const = Const of 'a

(** OCaml doesn't have a built in either type *)
type ('a, 'b) either =
  | Left of 'a
  | Right of 'b (** Either type *)

type 'a option = ((unit, 'a) const, 'a id) either
