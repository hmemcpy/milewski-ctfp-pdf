module Process_Do = (W: Monad_Bind with type m('a) = 
    writer(string, 'a)) => {
  /* Needs Reason parser >= 3.6.0 */
  let (let*) = W.(>>=);

  let process = s => {
    let* up_str = up_case(s);
    to_words(up_str);
  };
};
