process :: String -> Writer String [String]
process = upCase >=> toWords