module type List_Functor_Type = sig
  type 'a t = 'a list

  val fmap : ('a -> 'b) -> 'a list -> 'b list
end
