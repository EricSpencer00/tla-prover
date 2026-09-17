----- MODULE mathd_numbertheory_296 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_296 ==
    \A n \in Nat :
        (n >= 2) /\
        (\E x \in Nat : x * x * x = n) /\
        (\E t \in Nat : t * t * t * t = n) =>
        (4096 <= n)
BY SetExtensionality
===============================================================
