(* Import Str module using this - #require "str" *)
let to_words s = Writer (Str.split (Str.regexp "\b") s, "to_words")

module Writer_Process (W : Monad with type 'a m = (string, 'a) writer) =
struct
  let process = W.(up_case >=> to_words)
end
