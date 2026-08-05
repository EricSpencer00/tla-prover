---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One
One == [num |-> 1, den |-> 1]

VARIABLES p

VARIABLES Init
Init == p = One

VARIABLES Half
Half == [num |-> p.num, den |-> p.den * 2]

VARIABLES Norm
Norm == IF p.num % 2 = 0 /\ p.den % 2 = 0
          THEN [num |-> p.num \div 2, den |-> p.den \div 2]
          ELSE p

VARIABLES Next
Next == Half \/ Norm

VARIABLES Spec
Spec == Init \/ Next

VARIABLES Inv
Inv == p.den >= 1

VARIABLES TypeOK
TypeOK == p \in [num : INTEGER, den : INTEGER]

====