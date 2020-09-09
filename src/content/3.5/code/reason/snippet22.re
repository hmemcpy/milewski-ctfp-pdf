module OptionMonad: Monad_Bind = {
  type m('a) = option('a);

  let (>>=) =
    fun
    | Some(a) => (k => k(a))
    | None => (_ => None);

  let return = a => Some(a);
};
