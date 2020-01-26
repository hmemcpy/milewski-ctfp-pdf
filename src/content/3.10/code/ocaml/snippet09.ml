module EndsEqualizer (P : Profunctor) = struct
  let lambda : 'a 'b. ('a, 'a) P.p -> ('a -> 'b) -> ('a, 'b) P.p =
   fun paa f -> P.dimap id f paa
 ;;

  let rho : 'a 'b. ('b, 'b) P.p -> ('a -> 'b) -> ('a, 'b) P.p =
   fun pbb f -> P.dimap f id pbb
 ;;
end
