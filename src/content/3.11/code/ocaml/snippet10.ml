module FreeFunctor (F : sig
  type 'a f
end) : Functor = struct
  module type F = FreeF with type 'a f = 'a F.f

  type 'a t = (module F with type a = 'a)

  let fmap
      (type a' b')
      (f : a' -> b')
      (module FF : F with type a = a')
    =
    (module struct
      type 'a f = 'a F.f
      type a = b'
      type i = FF.i

      let h i = f (FF.h i)
      let fi = FF.fi
    end : F
      with type a = b')
  ;;
end
