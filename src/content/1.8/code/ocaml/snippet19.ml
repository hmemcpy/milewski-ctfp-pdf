module KleisliFunctor : Functor = struct
  type 'a t = 'a writer

  let fmap f =
    KleisliComposition.( >=> ) id (fun x ->
        KleisliIdentity.return (f x))
  ;;
end
