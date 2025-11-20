module StreamFunctor : Functor with type 'a t = 'a stream = struct
  type 'a t = 'a stream

  let rec fmap f (Cons (x, xs)) =
    Cons (f x, Lazy.from_val (fmap f (Lazy.force xs)))
end
