module BindUsingFunctionAndJoin (F : Functor) = struct
  type 'a m = 'a F.t

  external join : 'a m m -> 'a m = "%identity"
  (** Make the type signature of join work 
  without providing an implementation **)

  let ( >>= ) ma f = join (F.fmap f ma)
end
