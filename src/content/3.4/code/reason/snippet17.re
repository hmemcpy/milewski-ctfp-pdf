/* Import Str module using this - #require "str" */
let to_words = s => Writer(Str.split(Str.regexp("\b"), s), "to_words");

module Writer_Process = (W: Monad with type m('a) = 
    writer(string, 'a)) => {
  let process = W.(up_case >=> to_words);
};
