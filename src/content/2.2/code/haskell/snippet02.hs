contramap :: (c' -> c) -> (c -> LimD) -> (c' -> LimD) 
contramap f u = u . f