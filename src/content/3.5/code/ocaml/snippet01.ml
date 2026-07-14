(* For infinite lists, like in Haskell, we use the [Seq] module. *)
module Seq_Monad : Monad_Join with type 'a t = 'a Seq.t = struct
  type 'a t = 'a Seq.t

  let join = Seq.concat

  (* [Seq] already has a [return] function. *)
  let return a = Seq.return a
end
