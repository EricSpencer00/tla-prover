---- MODULE amc12b_2002_p2 ----
EXTENDS Integers, TLAPS

THEOREM amc12b_2002_p2 ==
    \A x \in Int :
        (x = 4) => (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11BY SMT
====
