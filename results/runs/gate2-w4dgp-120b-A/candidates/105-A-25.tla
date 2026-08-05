---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init == p = [num |-> 1, den |-> 1]

Next == \E q \in { [num |-> p.num, den |-> p.den * 2], [num |-> p.num \div 2, den |-> p.den \div 2] } :
          p' = IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE q

Spec == Init /\ [][Next]_vars

Inv == p \in { [num |-> 1, den |-> 1] } \/ (p.num \in (Nat \ {0}) /\ p.den \in (Nat \ {0}))
====