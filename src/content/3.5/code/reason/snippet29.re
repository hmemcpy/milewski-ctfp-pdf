module Cont_Monad = (R: {type t;}) : Monad_Bind => {
  type m('a) = cont(R.t, 'a);

  let return = a => Cont(ha => ha(a));

  let (>>=) = (ka, kab) =>
    Cont(hb => run_cont(ka, a => run_cont(kab(a), hb)));
};
