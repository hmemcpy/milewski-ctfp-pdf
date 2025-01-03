module KleisliIdentity = struct
  let return (x : 'a) : 'a writer = (x, "")
end
