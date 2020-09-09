/* Monad implementation for type io */
module IOMonad: Monad_Bind with type m('a) = io('a) = {
  type m('a) = io('a);

  let return = x => IO(() => x);

  let (>>=) = (m, f) => IO(() => {
    let IO(m') = m;
    let IO(m'') = f(m'());
    m''();
  });
};

/* main */
module IO_Main = {
  let (let*) = IOMonad.(>>=);

  let main = {
    let* _ = put_str("Hello");
    put_str("world!");
  };
};
