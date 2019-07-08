module Process_Bind_Without_Do
    (W : Monad_Bind with type 'a m = (string, 'a) writer) =
struct
  open Monad_Ops (W)

  let tell w = Writer ((), w)

  let process s =
    W.(
      up_case s >>= fun up_str -> tell "to_words" >> to_words up_str)
end
