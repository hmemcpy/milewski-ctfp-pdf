module Reader_Functor (T : T) : Functor with type 'a t = T.t -> 'a = struct
  type 'a t = T.t -> 'a

  let fmap f ra r = f (ra r)
end
