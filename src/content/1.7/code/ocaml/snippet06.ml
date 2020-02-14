module type Maybe_Functor = sig
  type a
  type b

  val fmap : (a -> b) -> a option -> b option
end
