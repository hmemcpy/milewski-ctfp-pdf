(* Defining words and tell functions *)
let words s = String.split_on_char ' ' s
let tell w = Writer ((), w)

module Process_Tell
    (W : Monad_Bind with type 'a t = (string, 'a) writer) =
struct
  open W

  (* Needs OCaml compiler >= 4.08 *)
  let ( let* ) = ( >>= )

  let process s =
    let* up_str = up_case s in
    let* () = tell "to_words " in
    return (words up_str)
end
