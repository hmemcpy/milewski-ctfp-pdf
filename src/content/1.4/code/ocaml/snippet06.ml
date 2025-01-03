let up_case (s : string) : string writer =
  (String.uppercase_ascii s, "up_case ")

let to_words (s : string) : string list writer =
  (String.split_on_char ' ' s, "to_words ")
