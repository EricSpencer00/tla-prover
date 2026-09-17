---- MODULE amc12b_2002_p7 ----
EXTENDS Naturals, TLAPS

THEOREM amc12b_2002_p7 ==
    \A a, b, c \in Nat \ {0} :
        (b = a + 1 /\ c = b + 1 /\ a * b * c = 8 * (a + b + c)) => (a * a + b * b + c * c = 77)BY SetExtensionality
====
