let to_words: string => writer(list(string)) = (
  s => (String.split(s, ~on=' '), "to_words "):
    string => writer(list(string))
);
