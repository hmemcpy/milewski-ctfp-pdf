Fun.compose g f (* Since OCaml 5.2 *)

(* Alternatively, you can also define it as follows: *)
let compose f g x = f (g x)

(* Or even as an infix operator: *)
let ( % ) = Fun.compose (* Like in the Batteries library *)
