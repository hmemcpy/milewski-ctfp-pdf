(** OCaml doesn't support higher kinded types. So, we have to use
    module functors to emulate the behavior higher kinded types.
    There's less verbose options using type defunctionalization
    but it's more advanced and obscures the flow of this book *)
module type BiComp = functor
  (BF : sig
     type ('a, 'b) t
   end)
  (FU : sig
     type 'a t
   end)
  (GU : sig
     type 'b t
   end)
  -> sig
  type ('a, 'b) bicomp = BiComp of ('a FU.t, 'b GU.t) BF.t
end
