module Monad_Ops (M : Monad_Bind) = struct
  let ( >> ) m k = M.(m >>= fun _ -> k)
end
