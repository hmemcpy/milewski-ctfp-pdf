(* For lazy/infinite lists like in Haskell,
   we can use the [Seq] module. *)
let nats = Seq.ints 1 (* Equivalent to [1..] in Haskell *)
