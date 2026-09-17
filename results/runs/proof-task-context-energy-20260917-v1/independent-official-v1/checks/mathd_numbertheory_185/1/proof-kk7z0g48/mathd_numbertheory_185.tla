---- MODULE mathd_numbertheory_185 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_185 ==
    \A n \in Nat : (n % 5 = 3) => (2 * n) % 5 = 1BY SetExtensionality
====
