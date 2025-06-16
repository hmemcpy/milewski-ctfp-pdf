module ReaderMonad (T : sig
  type t
end) : Monad_Bind with type 'a t = (T.t, 'a) reader = struct
  type 'a t = (T.t, 'a) reader

  let ( >>= ) ra k =
    Reader (fun e -> run_reader (k (run_reader ra e)) e)
  let return a = Reader (fun e -> a)
end
