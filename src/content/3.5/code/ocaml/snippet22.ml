module OptionMonad : Monad_Bind = struct
  type 'a m = 'a option

  let ( >>= ) = function
    | Some a -> fun k -> k a
    | None   -> fun _ -> None


  let return a = Some a
end
