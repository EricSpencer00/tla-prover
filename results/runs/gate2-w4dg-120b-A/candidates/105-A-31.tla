---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES val

vars == <<val>>

Dyadic == [num : Nat, den : Nat]

RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

Init == val = One

Next == \E q \in Dyadic : val' = Norm(q)

Spec == Init /\ [][Next]_vars

TypeOK == /\ One \in Dyadic
          /\ Half \in Dyadic
          /\ val \in Dyadic

ValueInRange == val.den >= 1

====