module type NT_AX_FX = sig
  type a
  type 'x t

  val alpha : 'x. (int -> 'x) -> 'x t
end
