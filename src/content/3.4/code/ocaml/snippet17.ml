let up_case s = Writer (String.uppercase_ascii s, "up_case ")
let to_words s = Writer (String.split_on_char ' ' s, "to_words ")

module Writer_Process
    (W : Monad with type 'a t = (string, 'a) writer) =
struct
  open W

  let process = up_case >=> to_words
end
