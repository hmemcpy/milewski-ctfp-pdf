class Comonoid m where
    split :: m -> (m, m)
    destroy :: m -> ()