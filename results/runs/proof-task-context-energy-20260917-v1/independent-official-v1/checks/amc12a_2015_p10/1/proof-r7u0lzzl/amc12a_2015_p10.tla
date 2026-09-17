----- MODULE amc12a_2015_p10 -----
EXTENDS Integers, TLAPS

THEOREM amc12a_2015_p10 ==
    \A x, y \in Int :
        (y > 0) /\ (x > y) /\ (x + y + x * y = 80) => x = 26BY SMT
====
