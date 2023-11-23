prodToSum : (a × Either b c) → Either (a × b) (a × c)
prodToSum (x , Left y)  = Left (x , y)
prodToSum (x , Right z) = Right (x , z)
