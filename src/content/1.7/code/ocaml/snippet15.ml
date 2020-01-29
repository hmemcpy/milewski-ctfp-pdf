module Option_Functor : Functor with type 'a t = 'a option = struct
  type 'a t = 'a option

  let fmap f = function
    | None -> None
    | Some x -> Some (f x)
  ;;
end
