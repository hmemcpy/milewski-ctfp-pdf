let tail (Cons (_, xs)) = Lazy.force xs
