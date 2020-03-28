module C_to_CT = (T: Monad) => {
  let on_objects = T.return <.> f;
};
