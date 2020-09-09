module KleisiExample =
       (K: Kleisli
          with type a = string
          and type b = string
          and type c = list(string)
       ) => {
  let up_case_and_to_words: string => writer(list(string)) = (
    K.(>=>)(up_case, to_words): string => writer(list(string))
  );
};
