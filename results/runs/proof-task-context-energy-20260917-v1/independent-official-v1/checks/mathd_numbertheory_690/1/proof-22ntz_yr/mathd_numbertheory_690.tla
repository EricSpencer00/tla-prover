---------------------------- MODULE mathd_numbertheory_690 ---------------------------
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_690 ==
    \A a \in Nat \ {0} :
        (a % 3 = 2 /\ a % 5 = 4 /\ a % 7 = 6 /\ a % 9 = 8) => (a >= 314)BY SMT
=============================================================================
