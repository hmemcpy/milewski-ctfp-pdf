alpha :: forall x. (Int -> x) -> [x]
alpha h = map h [12]