(* OCaml doesn't ship with a lazy sequence range syntax nor a product
   function; defining our own. *)

let rec range seq n1 n2 =
  if n2 < n1 then seq
  else n2 |> pred |> range (fun () -> Seq.Cons (n2, seq)) n1
let range = range Seq.empty

let rec product result seq = match seq () with
  | Seq.Nil -> result
  | Seq.Cons (n, seq) -> product (result * n) seq
let product = product 1

let fact n = product (range 1 n)
