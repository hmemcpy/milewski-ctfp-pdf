(* Defining the bind operator for let* syntax sugar *)
let ( let* ) = ( >>= )

(* The triples function can thus be defined as follows
   using the bind operator we defined previously and the
   return function from the [Seq] module, assuming that
   the [guard] function is defined as well. *)
let triples =
  let* z = Seq.ints 1 in
  let* x = Seq.take z (Seq.ints 1) in
  let* y = Seq.take (z - x) (Seq.ints x) in
  let* () = guard ((x * x) + (y * y) = z * z) in
  Seq.return (x, y, z)
