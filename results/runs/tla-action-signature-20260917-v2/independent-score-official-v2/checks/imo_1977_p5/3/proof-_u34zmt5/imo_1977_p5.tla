----- MODULE imo_1977_p5 -----
EXTENDS TLAPS, Integers

ABS(n) == IF n < 0 THEN -n ELSE n

THEOREM imo_1977_p5 ==
    \A a, b, q, r \in Int :
        (a >= 0 /\ b >= 0 /\ r >= 0 /\ q >= 0) /\
        (r < a + b /\ a * a + b * b = (a + b) * q + r /\ q * q + r = 1977) =>
        (ABS(a - 22) = 15 /\ ABS(b - 22) = 28) \/ (ABS(a - 22) = 28 /\ ABS(b - 22) = 15)BY DEF ABS
====
