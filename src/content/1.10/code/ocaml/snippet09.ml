let safe_head (fmap f (x :: xs)) = safe_head (f x :: f xs) = Some (f x)
