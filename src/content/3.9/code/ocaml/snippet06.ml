module C_to_CT (T : Monad) = struct
  let on_objects f = Fun.compose T.return f
end
