---- MODULE amc12a_2002_p6 ----
EXTENDS TLAPS, Integers

THEOREM amc12a_2002_p6 ==
    \A n \in Nat \ {0} : \E m \in Nat :
        (m > n) /\ (\E p \in Nat : m * p <= m + p)BY NoSetContainsEverything
====
