---- MODULE numbertheory_notequiv2i2jasqbsqdiv8 ----
EXTENDS Integers, TLAPS

Divides(a, b) == \E k \in Int : b = a * k

THEOREM numbertheory_notequiv2i2jasqbsqdiv8 ==
    ~\A a, b \in Int :
        ((\E i, j \in Int : a = 2 * i \land b = 2 * j) <=>
         (\E k \in Int : a*2 + b*2 = 8 * k))BY SMT, SetExtensionality
====
