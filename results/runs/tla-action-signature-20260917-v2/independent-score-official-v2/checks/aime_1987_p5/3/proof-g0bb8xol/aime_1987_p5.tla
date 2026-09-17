---- MODULE aime_1987_p5 ----
EXTENDS TLAPS, Integers

THEOREM aime_1987_p5 ==
    \A x, y \in Int : y * y + 3*(x * x)*(y * y) = 30*(x * x) + 517 => 3*(x * x)*(y * y) = 588BY SMT, SetExtensionality, NoSetContainsEverything
====
