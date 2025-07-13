module KleisliFunctor : Functor with type 'a t = 'a writer = struct
  open KleisliComposition
  open KleisliIdentity

  type 'a t = 'a writer

  let fmap f = Fun.id >=> fun x -> return (f x)
end
