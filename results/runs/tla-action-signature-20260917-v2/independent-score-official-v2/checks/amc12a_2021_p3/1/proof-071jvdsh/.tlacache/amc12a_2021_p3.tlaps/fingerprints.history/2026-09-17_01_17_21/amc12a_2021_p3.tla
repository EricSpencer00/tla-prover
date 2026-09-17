----- MODULE amc12a_2021_p3 -----
EXTENDS Naturals, TLAPS

THEOREM amc12a_2021_p3 ==
    \A x, y \in Nat :
        x + y = 17402 /\ (x = 10 * y) => (x - y = 14238)BY SMT
====
