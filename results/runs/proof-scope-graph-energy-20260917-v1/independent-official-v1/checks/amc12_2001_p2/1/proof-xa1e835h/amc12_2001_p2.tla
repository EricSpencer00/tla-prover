----- MODULE amc12_2001_p2 -----
EXTENDS TLAPS, Naturals

THEOREM amc12_2001_p2 ==
    \A a, b, n \in Nat :
        (1 <= a) /\ (a <= 9) /\ (0 <= b) /\ (b <= 9) /\ (n = 10 * a + b) /\ (n = a * b + a + b) => (b = 9)BY SetExtensionality
====
