process : String → Writer (List String)
process = upCase >=> toWords
