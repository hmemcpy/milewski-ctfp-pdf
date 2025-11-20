let ( >>= ) seq f = Seq.concat (Seq.map f seq)
