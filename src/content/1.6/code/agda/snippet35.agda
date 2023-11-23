sumToProd : Either (a × b) (a × c) → (a × Either b c)
sumToProd (Left (x , y))  = x , Left y
sumToProd (Right (x , z)) = x , Right z
