---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANT One
CONSTANT Half
CONSTANT Norm

Specification == TRUE

VARIABLES p
vars == <<p>>

Init == p = One

Next == p' = IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

TypeOK ==
    /\ p \in [num : Int, den : Int]

Spec == Init /\ [][Next]_vars

Invar == TRUE

Prop == TRUE
====