---- MODULE aime_1991_p1 ----
EXTENDS Naturals, TLAPS

THEOREM aime_1991_p1 ==
    \A x, y \in Nat \ {0} :
        (x * y + x + y = 71) /\ (x * x * y + x * y * y = 880) => (x * x + y * y = 146)BY SetExtensionality
====
