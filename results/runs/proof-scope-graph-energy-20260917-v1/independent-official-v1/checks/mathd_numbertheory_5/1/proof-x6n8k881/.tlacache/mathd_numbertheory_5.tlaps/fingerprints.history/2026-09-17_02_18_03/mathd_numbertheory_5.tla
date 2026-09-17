----- MODULE mathd_numbertheory_5 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_5 ==
    \A n \in Nat :
        n >= 10 /\
        (\E x \in Nat : x * x = n) /\
        (\E t \in Nat : t * t * t = n) =>
        n >= 64
BY SetExtensionality
=============================================================================
