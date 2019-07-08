module ReaderMonad (T : sig
  type t
end) : Monad_Bind = struct
  type 'a m = (T.t, 'a) reader

  let return a = Reader (fun e -> a)

  let ( >>= ) ra k =
    Reader (fun e -> run_reader (k (run_reader ra e)) e)
end
