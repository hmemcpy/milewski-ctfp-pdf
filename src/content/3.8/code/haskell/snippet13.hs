unFix :: Fix f -> f (Fix f)
unFix (Fix x) = x