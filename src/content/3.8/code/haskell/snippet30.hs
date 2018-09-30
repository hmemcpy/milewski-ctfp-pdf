toListC :: Fix (StreamF e) -> [e]
toListC = cata al
    where al :: StreamF e [e] -> [e] 
          al (StreamF e a) = e : a