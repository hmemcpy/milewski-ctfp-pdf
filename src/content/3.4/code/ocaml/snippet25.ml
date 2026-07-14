module Process_Bind_Without_Do
    (W : Monad_Bind with type 'a t = (string, 'a) writer) =
struct
  open W
  open Monad_Ops (W)

  let tell w = Writer ((), w)
  let process s =
    up_case s >>= fun up_str -> tell "to_words" >> to_words up_str
end
