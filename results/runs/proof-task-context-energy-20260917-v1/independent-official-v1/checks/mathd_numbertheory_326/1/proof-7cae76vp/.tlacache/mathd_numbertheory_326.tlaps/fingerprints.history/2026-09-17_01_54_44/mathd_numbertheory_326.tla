---- MODULE mathd_numbertheory_326 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_326 ==
    \A n \in Int :
        ((n - 1) * n * (n + 1) = 720) => (n + 1 = 10)BY SMT
====
