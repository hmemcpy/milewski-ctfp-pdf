(* Note: in OCaml, strings are not equivalent to char lists.
   Strings are treated as immutable sequences of bytes, while
   a char list is a linked list of characters. *)
type string = char list
