let contramap : ('b -> 'a) -> ('r, 'a) op -> ('r, 'b) op =
 fun f g -> flip compose f g
;;
