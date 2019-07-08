let ( >>= ) xs k = List.concat (List.map k xs)
