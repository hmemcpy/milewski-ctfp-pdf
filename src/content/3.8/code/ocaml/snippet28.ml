(* Extract the head of a sequence *)
let seq_hd_exn seq =
  match seq () with
  | Seq.Nil -> failwith "Empty sequence"
  | Seq.Cons (p, ns) -> p

(* For Haskell-like infinite lists,
   we'll use OCaml's sequences instead *)
let era (seq : int Seq.t) : (int, int Seq.t) stream_f =
  let notdiv p n = n mod p <> 0 in
  let p = seq_hd_exn seq in
  StreamF (p, lazy (Seq.filter (notdiv p) seq))
