module Fixpoint (F : Functor) = struct
  type 'a t = Fix of 'a t F.t

  let unfix (Fix f) : 'a t F.t = f
end

(* For a complete type signature, it could be something like: *)
module type Fixpoint = sig
  type 'a funct
  type 'a t = Fix of 'a t funct

  val fix : 'a t funct -> 'a t
  val unfix : 'a t -> 'a t funct
end
