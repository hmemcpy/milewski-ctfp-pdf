let dumb : 'a. (unit, 'a) reader -> 'a option = function
  | Reader _ -> None
;;
