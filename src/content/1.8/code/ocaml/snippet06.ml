module Identity_Functor : Functor with type 'a t = 'a id = struct
  type 'a t = 'a id

  let fmap f (Id a) = Id (f a)
end
