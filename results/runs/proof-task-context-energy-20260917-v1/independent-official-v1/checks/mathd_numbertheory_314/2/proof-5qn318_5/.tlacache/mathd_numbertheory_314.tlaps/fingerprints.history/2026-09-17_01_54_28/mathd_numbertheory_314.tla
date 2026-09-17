----- MODULE mathd_numbertheory_314 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_314 ==
    \A r, n \in Nat :
        (n > 0) /\
        (r = 1342 % 13) /\
        (1342 % n = 0) /\
        (n % 13 < r)
        => (6710 <= n)
BY SetExtensionality
====
