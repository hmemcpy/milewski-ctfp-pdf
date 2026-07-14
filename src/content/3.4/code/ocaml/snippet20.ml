module Process_Bind_Without_Do
    (W : Monad_Bind with type 'a t = (string, 'a) writer) =
struct
  open W

  (* let* x = m in n is equivalent to m >>= fun x -> n *)
  let process s = up_case s >>= fun up_str -> to_words up_str
end
