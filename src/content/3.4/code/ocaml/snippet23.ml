module Process_Bind_Without_Do
    (W : Monad_Bind with type 'a t = (string, 'a) writer) =
struct
  open W

  let process s =
    up_case s >>= fun up_str ->
    tell "to_words" >>= fun () -> return (words up_str)
end
