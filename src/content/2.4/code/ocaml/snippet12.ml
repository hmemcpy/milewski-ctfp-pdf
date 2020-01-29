module type NT_ListX_IntX = sig
  type a = int
  type 'x t = 'x list

  val beta : 'x t -> a -> 'x
end
