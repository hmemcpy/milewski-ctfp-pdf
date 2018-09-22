process s =
  upCase s >>= \upStr ->
    tell "toWords " >>
      return (words upStr)