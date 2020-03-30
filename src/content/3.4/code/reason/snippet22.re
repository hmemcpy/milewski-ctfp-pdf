module Process_Tell = (W: Monad_Bind with type m('a) =
    writer(string, 'a)) => {
  /* Needs Reason parser >= 3.6.0 */
  let (let*) = W.(>>=);
  let tell = w => Writer((), w);

  let process = s => {
    let* up_str = up_case(s);
    let* _ = tell("to_words ");
    to_words(up_str);
  };
};
