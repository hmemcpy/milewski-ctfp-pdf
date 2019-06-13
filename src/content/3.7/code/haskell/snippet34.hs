unit :: a -> Reader s (Product a s)
unit a = Reader (\s -> Prod a s)