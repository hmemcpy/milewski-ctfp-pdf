module Process_Bind_Without_Do =
       (W: Monad_Bind with type m('a) = writer(string, 'a)) => {
  let process = s => W.(up_case(s) >>= (up_str => to_words(up_str)));
};
