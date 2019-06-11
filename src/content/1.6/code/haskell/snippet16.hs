tupleToElem :: (String, String, Int) -> Element
tupleToElem (n, s, a) = Element { name = n 
                                , symbol = s 
                                , atomicNumber = a }