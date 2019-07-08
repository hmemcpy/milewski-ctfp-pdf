module Process_Bind_Without_Do
    (W : Monad_Bind with type 'a m = (string, 'a) writer) =
struct
  let process s = W.(up_case s >>= fun up_str -> to_words up_str)
end
