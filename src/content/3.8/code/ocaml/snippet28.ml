(* OCaml library Gen provides infinite data structures *)
let era : int Gen.t -> (int, int Gen.t) stream_f =
 fun ilist ->
  let notdiv p n = n mod p != 0 in
  let p = Gen.get_exn ilist in
  StreamF (p, Gen.filter (notdiv p) ilist)
;;
