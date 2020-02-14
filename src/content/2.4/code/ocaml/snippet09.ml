module type NT_FX_AX = sig
  type a
  type 'x t

  val beta : 'x t -> a -> 'x
end
