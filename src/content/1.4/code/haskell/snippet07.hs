process :: String -> Writer [String]
process = upCase >=> toWords