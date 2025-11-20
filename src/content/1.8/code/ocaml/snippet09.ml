(** OCaml doesn't support higher kinded types. So, we have to use
    module functors to emulate the behavior higher kinded types.
    There's less verbose options using type defunctionalization
    but it's more advanced and obscures the flow of this book *)
module type BiCompBifunctor = functor
  (BF : Bifunctor)
  (FU : Functor)
  (GU : Functor)
  -> Bifunctor
