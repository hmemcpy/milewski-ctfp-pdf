let up_case : string -> string writer =
 fun s -> String.uppercase s, "up_case "
;;

let to_words : string -> string list writer =
 fun s -> String.split s ~on:' ', "to_words "
;;
