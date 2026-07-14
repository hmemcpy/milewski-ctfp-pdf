(** OCaml doesn't have a compose operator. So, creating one. **)
let ( % ) g f x = g (f x)
g % f
