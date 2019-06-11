process s = do
    upStr <- upCase s
    tell "toWords "
    return (words upStr)