let up_case: string => writer(string) =
  s => (String.uppercase(s), "up_case ");

let to_words: string => writer(list(string)) =
  s => (String.split(s, ~on=' '), "to_words ");kkkk
