----- MODULE imo_1992_p1 -----
EXTENDS Integers, TLAPS

Divides(a, b) == \E k \in Int : b = k * a

THEOREM imo_1992_p1 ==
    \A p, q, r \in Int :
        (1 < p) /\ (p < q) /\ (q < r) /\
        Divides((p - 1) * (q - 1) * (r - 1), p * q * r - 1) =>
        (p = 2 /\ q = 4 /\ r = 8) \/ (p = 3 /\ q = 5 /\ r = 15)BY SMT DEF Divides
====
