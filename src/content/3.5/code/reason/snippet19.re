module State_Monad = (S: {type t;}) : Monad_Bind => {
  type m('a) = state(S.t, 'a);

  let (>>=) = (sa, k) => State(s => {
    let (a, s') = run_state(sa, s);
    let sb = k(a);
    run_state(sb, s');
  });

  let return = a => State(s => (a, s));
};
