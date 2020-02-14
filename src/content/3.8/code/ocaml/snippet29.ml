module Stream_Int = Stream_Functor (struct
  type e = int
end)

module Ana_Stream = Ana (Stream_Int)

(* The fixpoint translated to OCaml is eager in its evaluation. 
Hence, executing the following function will cause overflow.
So, wrapping it inside a lazy *)
let primes = lazy (Ana_Stream.ana era (Gen.init (fun i -> i + 2)))
