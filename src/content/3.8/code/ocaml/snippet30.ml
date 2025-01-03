(* We can also make the Cata module for an int stream *)
module Stream_Cata = Cata (Stream_Functor_Int) (Fix)

let to_seq_c : int Seq.t Fix.t -> int Seq.t =
  let al (StreamF (e, a)) = fun () -> Seq.Cons (e, Lazy.force a) in
  Stream_Cata.cata al

let list_primes = to_seq_c primes
