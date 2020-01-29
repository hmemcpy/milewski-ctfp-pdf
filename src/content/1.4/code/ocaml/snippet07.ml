module KleisiExample
    (K : Kleisli
           with type a = string
            and type b = string
            and type c = string list) =
struct
  let up_case_and_to_words : string -> string list writer =
    K.( >=> ) up_case to_words
  ;;
end
