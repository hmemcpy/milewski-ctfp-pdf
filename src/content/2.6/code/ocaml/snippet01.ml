module type BtoA = sig
  type a
  type b

  val btoa : b -> a
end

(* Define the Yoneda embedding *)
module Yoneda_Embedding (E : BtoA) = struct
  let fromY (f : E.a -> 'x) (b : E.b) : 'x = f (E.btoa b)
end
