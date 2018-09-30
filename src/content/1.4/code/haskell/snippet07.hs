toWords :: String -> Writer [String]
toWords s = (words s, "toWords ")