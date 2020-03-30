module ReaderMonad = (T: {type t;}) : Monad_Bind => {
  type m('a) = reader(T.t, 'a);

  let return = a => Reader(e => a);

  let (>>=) = (ra, k) => 
    Reader(e => run_reader(k(run_reader(ra, e)), e));
};
