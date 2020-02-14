module Process_Tell
    (W : Monad_Bind with type 'a m = (string, 'a) writer) =
struct
  (* Needs OCaml compiler >= 4.08 *)
  let ( let* ) = W.( >>= )
  let tell w = Writer ((), w)

  let process s =
    let* up_str = up_case s in
    let* _ = tell "to_words " in
    to_words up_str
end
