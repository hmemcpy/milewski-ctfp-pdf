type ('c, 'a) const = Const of 'c

(* Assuming you've defined un_const before this function *)
let rec length : 'a list -> (int, 'a) const = function
  | [] -> Const 0
  | _ :: xs -> Const (1 + un_const (length xs))
