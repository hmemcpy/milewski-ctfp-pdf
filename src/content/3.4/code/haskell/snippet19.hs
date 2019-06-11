upCase :: String -> Writer String String
upCase s = Writer (map toUpper s, "upCase ")