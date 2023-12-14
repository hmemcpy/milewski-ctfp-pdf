fmap f nothing = nothing
fmap f (just x) = just (f x)
