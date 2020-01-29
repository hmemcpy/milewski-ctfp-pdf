let scam : 'a. ('int, 'a) const -> 'a option = function
  | Const a -> None
;;
