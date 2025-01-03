(* OCaml does not have typeclasses, but we can simulate
   them with modules. *)
module type Eq = sig
  type a

  val ( == ) : a -> a -> bool
end
