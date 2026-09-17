----- MODULE aime_1994_p3 -----
EXTENDS Integers, TLAPS

THEOREM aime_1994_p3 ==
    \A x \in Int : \A f \in [Int -> Int] : (f[x] + f[x - 1] = x * x) /\ (f[19] = 94) => (f[94] % 1000 = 561)BY SetExtensionality
===============================================================
