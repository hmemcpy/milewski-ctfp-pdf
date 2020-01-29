module C_to_CT (T : Monad) = struct
  let on_objects = T.return <.> f
end
