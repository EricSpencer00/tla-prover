---- MODULE mathd_numbertheory_430 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_430 ==
    \A a, b, c \in {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} :
        (a # b) /\ (a # c) /\ (b # c) /\
        (a + b = c) /\
        (10 * a + a - b = 2 * c) /\
        (c * b = 10 * a + a + a)
        => (a + b + c = 8)BY SetExtensionality
====
