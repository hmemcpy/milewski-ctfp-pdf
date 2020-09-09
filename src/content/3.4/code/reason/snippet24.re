module Monad_Ops = (M: Monad_Bind) => {
  let (>>) = (m, k) => M.(m >>= (_ => k));
};
