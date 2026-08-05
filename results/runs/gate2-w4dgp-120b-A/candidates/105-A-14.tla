---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init ==
  p = One

Next ==
  \/ p' = Half
  \/ p' = Norm

TypeInv == p \in [num : Int, den : Int]

Spec == Init /\ [][Next]_vars

NormSpec == \A p \in [num : Int, den : Int] : Norm(p) = IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p
====