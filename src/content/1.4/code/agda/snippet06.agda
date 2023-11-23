upCase : String → Writer String
upCase s = ( map toUpper s , "upCase " )

toWords : String → Writer (List String)
toWords s = ( words s , "toWords " )
