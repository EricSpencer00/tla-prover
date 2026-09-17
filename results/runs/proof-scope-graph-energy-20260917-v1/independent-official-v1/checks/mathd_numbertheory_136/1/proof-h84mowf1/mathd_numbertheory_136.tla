---- MODULE mathd_numbertheory_136 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_136 ==
    \A n \in Nat : (123 * n + 17 = 39500) => (n = 321)BY SetExtensionality
====
