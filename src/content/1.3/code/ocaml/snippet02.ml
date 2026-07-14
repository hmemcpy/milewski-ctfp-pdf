(* In OCaml, any module that defines a module type's members,
   automatically conforms to that module type. It doesn't need to
   explicitly declare that it conforms. *)

type t = string

let mempty = ""
let mappend = ( ^ )
