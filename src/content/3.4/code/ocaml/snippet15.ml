module Fmap_Using_Monad (M : Monad_Bind) = struct
  let fmap f ma = M.( >>= ) ma (fun a -> M.return (f a))
end
