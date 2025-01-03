module BindUsingFunctionAndJoin (F : Functor) = struct
  type 'a m = 'a F.t

  (* Assuming that join is defined before *)
  let ( >>= ) ma f = join (F.fmap f ma)
end
