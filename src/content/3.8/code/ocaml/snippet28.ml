(* OCaml library `gen` provides useful helpers for 
   potentially infinite iterators. You can install it
   with `opam install gen`. To use it in the toplevel,
   you need to `#require "gen"` *)
let era : int Gen.t -> (int, int Gen.t) stream_f =
 fun ilist ->
  let notdiv p n = n mod p != 0 in
  let p = Gen.get_exn ilist in
  StreamF (p, Gen.filter (notdiv p) ilist)
;;
