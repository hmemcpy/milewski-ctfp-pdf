process s = 
    upCase s >>= \upStr ->
        toWords upStr