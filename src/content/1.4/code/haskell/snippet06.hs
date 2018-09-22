upCase :: String -> Writer String
upCase s = (map toUpper s, "upCase ")