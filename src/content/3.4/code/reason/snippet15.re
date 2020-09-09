module Fmap_Using_Monad = (M: Monad_Bind) => {
  let fmap = (f, ma) => M.(>>=)(ma, a => M.return(f(a)));
};
