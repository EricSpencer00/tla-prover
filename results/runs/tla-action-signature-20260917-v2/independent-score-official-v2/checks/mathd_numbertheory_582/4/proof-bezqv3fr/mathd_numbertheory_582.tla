---- MODULE mathd_numbertheory_582 ----
EXTENDS TLAPS, Integers

Divides(a, b) == \E k \in Nat : b = a * k

THEOREM mathd_numbertheory_582 ==
    \A n \in Nat \ {0} :
        Divides(3, n)
        => (n + 4 + (n + 6) + (n + 8)) % 9 = 0BY SMT, SetExtensionality
====
