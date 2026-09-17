---- MODULE mathd_numbertheory_48 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_48 ==
    \A b \in Nat : (b > 0) /\ (3 * b * b + 2 * b + 1 = 57) => (b = 4)
BY SetExtensionality
====
