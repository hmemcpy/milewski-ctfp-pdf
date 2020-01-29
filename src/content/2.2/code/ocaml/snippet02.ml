let contramap : ('c_prime -> 'c) -> ('c -> 'limD) -> 'c_prime -> 'limD
  =
 fun f u -> compose u f
;;
