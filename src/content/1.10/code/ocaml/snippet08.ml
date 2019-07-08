let fmap f (safe_head (x :: xs)) = fmap f (Some x)= Some (f x)
