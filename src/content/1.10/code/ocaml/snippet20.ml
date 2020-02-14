let obvious : 'a. (unit, 'a) reader -> 'a option = function
  | Reader f -> Some (f ())
;;
