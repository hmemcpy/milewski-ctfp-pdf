module List_Monad : Monad_Join = struct
  type 'a m = 'a list

  let join = List.concat
  let return a = [ a ]
end
