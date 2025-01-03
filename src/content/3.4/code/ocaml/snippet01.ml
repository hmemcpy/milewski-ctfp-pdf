let ( % ) = Fun.compose

(* There's no sum function in the List module *)
let sum = List.fold_left ( +. ) 0.

(* The vlen function, like the Haskell version, using
   List.map as the list functor fmap *)
let vlen = sqrt % sum % List.map (Fun.flip ( ** ) 2.)
