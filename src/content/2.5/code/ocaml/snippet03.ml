module type NT_AX_FX = sig
  type a
  type 'x t

  val alpha : (a -> 'x) -> 'x t
end
