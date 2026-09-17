---- MODULE amc12a_2003_p5 ----
EXTENDS Naturals, TLAPS

THEOREM amc12a_2003_p5 ==
    \A A, M, C \in Nat :
        (A <= 9) /\ (M <= 9) /\ (C <= 9) /\
        (1000 + 100 * C + 10 * M + A + 21000 + 100 * C + 10 * M + A = 123422) => (A + M + C = 14)BY SMT
====
