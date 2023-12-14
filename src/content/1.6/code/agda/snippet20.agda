startsWithSymbol e = symbol e isPrefixOf name e
-- In Agda, we use underscores to denote the positions of
-- infix arguments; here, the function declaration would be
_isPrefixOf_ : String → String → Bool
