module OptionMonad : Monad_Bind with type 'a t = 'a option = struct
  type 'a t = 'a option

  let ( >>= ) = function
    | Some a -> fun k -> k a
    | None   -> fun _ -> None

  let return a = Some a
end
