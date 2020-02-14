module NT_Impl (F : Functor with type 'a t = 'a list) :
  NT_AX_FX with type a = int and type 'x t = 'x list = struct
  type a = int
  type 'x t = 'x list

  let alpha : 'x. (int -> 'x) -> 'x list = fun h -> F.fmap h [ 12 ]
end
