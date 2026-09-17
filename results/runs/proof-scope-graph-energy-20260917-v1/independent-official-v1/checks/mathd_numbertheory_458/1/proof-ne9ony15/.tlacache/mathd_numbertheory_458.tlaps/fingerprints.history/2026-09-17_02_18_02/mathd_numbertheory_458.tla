----- MODULE mathd_numbertheory_458 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_458 ==
    \A n \in Nat : (n % 8 = 7) => (n % 4 = 3)BY SetExtensionality
=====================================================================================
