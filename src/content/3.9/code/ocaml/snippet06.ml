module C_to_CT (T : Monad) = struct
  let on_objects = compose T.return f
end
