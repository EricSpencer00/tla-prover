---- MODULE amc12_2000_p12 ----
EXTENDS Naturals, TLAPS

THEOREM amc12_2000_p12 ==
    \A a, m, c \in Nat :
        (a + m + c = 12) =>
        (a * m * c + a * m + m * c + a * c <= 112)BY SMT
====
