module type BtoA = sig
  type a
  type b

  val btoa : b -> a
end

(* Define the Yoneda embedding *)
module Yoneda_Embedding (E : BtoA) = struct
  let fromY : 'x. (E.a -> 'x) -> E.b -> 'x = fun f b -> f (E.btoa b)
end
