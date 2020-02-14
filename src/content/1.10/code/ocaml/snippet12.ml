(** OCaml requires mutually recursive functions to be defined together *)
let rec length : 'a list -> (int, 'a) const = function
  | [] -> Const 0
  | _ :: xs -> Const (1 + un_const (length xs))

and un_const : 'c 'a. ('c, 'a) const -> 'c = function
  | Const c -> c
;;
