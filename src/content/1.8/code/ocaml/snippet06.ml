module Identity_Functor : Functor = struct
  type 'a t = 'a id

  let fmap f (Id a) = Id (f a)
end
