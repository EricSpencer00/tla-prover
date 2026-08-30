---- MODULE DyadicRationals ----
Extends Integers

CONSTANTS One, Half

VARIABLES p

vars == <<p>>

RECURSIVE Norm(_)
Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
          ELSE q

Spec == p = One

TypeOK == p \in {[num : Int, den : Int]}

Init == Spec

Next == Spec

Invar == Spec

SpecProp == Spec

====