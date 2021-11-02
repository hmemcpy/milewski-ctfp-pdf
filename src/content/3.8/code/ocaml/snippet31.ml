(* Gen.t is used to represent infinite data structures like haskell's
   lazy list *)
val unfold : ('b -> ('a * 'b) option) -> 'b -> 'a Gen.t
