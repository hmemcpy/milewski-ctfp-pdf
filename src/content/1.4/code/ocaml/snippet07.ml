let process : string -> string list writer =
  up_case >=> to_words
