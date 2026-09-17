----- MODULE exercise_1_1_3 -----
EXTENDS Integers, TLAPS

THEOREM exercise_1_1_3 ==
    \A a, b, c, n \in Int :
        \E k \in Int :
            (a + b) + c - (a + (b + c)) = k * nBY SMT, NoSetContainsEverything, SetExtensionality
============================================
