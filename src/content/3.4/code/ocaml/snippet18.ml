module Process_Do
    (W : Monad_Bind with type 'a m = (string, 'a) writer) =
struct
  (* Needs OCaml compiler >= 4.08 *)
  let ( let* ) = W.( >>= )

  let process s =
    let* up_str = up_case s in
    to_words up_str
end
