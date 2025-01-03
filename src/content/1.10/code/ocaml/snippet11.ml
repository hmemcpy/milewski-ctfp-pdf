module OptionFunctor : Functor with type 'a t = 'a option = struct
  type 'a t = 'a option

  let fmap f = function
      | None -> None
      | Some x -> Some (f x)
end

(* As a reminder, note that in the OCaml Stdlib, the List
   and Option modules are already "Functors" in the sense
   that they have an fmap function (called map). Thus, the
   following fmaps do the same as the fmaps defined above. *)
let option_fmap f = Option.map f
let list_fmap f = List.map f
