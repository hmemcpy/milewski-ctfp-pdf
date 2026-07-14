(* val up_case : string -> string writer
   Note: OCaml strings are raw bytestrings, not UTF-8 encoded. *)
let up_case s = String.uppercase_ascii s, "up_case "

(* val to_words : string -> string list writer *)
let to_words s = String.split_on_char ' ' s, "to_words "
