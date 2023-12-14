predToStr (op f) = op λ x → if (f x) then "T" else "F"
