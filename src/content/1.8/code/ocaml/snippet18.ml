module KleisliIdentity = struct
  let return : 'a -> 'a writer = fun a -> a, ""
end
