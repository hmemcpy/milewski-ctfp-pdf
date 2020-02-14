module Ana (F : Functor) = struct
  type 'a fix = Fix of 'a fix F.t

  let rec ana : ('a -> 'a F.t) -> 'a -> 'a fix =
   fun coalg a -> Fix (F.fmap (ana coalg) (coalg a))
 ;;
end
