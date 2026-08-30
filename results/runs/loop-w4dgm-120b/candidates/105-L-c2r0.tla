---- MODULE DyadicRationals ----
EXTENDS Integers

Rep == [num : Int, den : Int]

One == [num |-> 1, den |-> 1]

Half(p) == IF p.den = 1 THEN [num |-> p.num, den |-> 2] ELSE [num |-> p.num, den |-> p.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES r1, r2

vars == <<r1, r2>>

TypeOK ==
  /\ r1 \in Rep
  /\ r2 \in Rep

Init ==
  /\ r1 = One
  /\ r2 = One

Specification ==
  /\ r1' = Half(r1)
  /\ r2' = Half(r2)

Next ==
  \/ Specification
  \/ /\ r1' = r1
     /\ r2' = r2

InitInv ==
  /\ r1 = One
  /\ r2 = One

ValueOne ==
  /\ r1 = [num |-> 1, den |-> 1]
  /\ r2 = [num |-> 1, den |-> 1]

NormInv ==
  /\ r1.num % 2 = 1 \/ r1.den % 2 = 1
  /\ r2.num % 2 = 1 \/ r2.den % 2 = 1

Spec == Init /\ [][Next]_vars

====