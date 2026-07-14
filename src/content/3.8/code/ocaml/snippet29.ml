(* Using the previous signature for Fixpoint *)
module Fixpoint (F : Functor) : Fixpoint
with type 'a funct = 'a F.t = struct
  type 'a funct = 'a F.t
  type 'a t = Fix of 'a t funct

  let fix (f : 'a t funct) : 'a t = Fix f
  let unfix (Fix f) : 'a t funct = f
end

(* Fixpoint for an int stream *)
module Fix = Fixpoint (Stream_Functor_Int)

(* We can make the Ana module for an int stream *)
module Stream_Ana = Ana (Stream_Functor_Int) (Fix)

let primes = Stream_Ana.ana era (Seq.ints 2)
