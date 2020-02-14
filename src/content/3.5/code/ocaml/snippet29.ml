module Cont_Monad (R : sig
  type t
end) : Monad_Bind = struct
  type 'a m = (R.t, 'a) cont

  let return a = Cont (fun ha -> ha a)

  let ( >>= ) ka kab =
    Cont (fun hb -> run_cont ka (fun a -> run_cont (kab a) hb))
end
