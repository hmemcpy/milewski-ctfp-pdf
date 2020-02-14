let moving_average n = StreamComonad.extend (average n)
