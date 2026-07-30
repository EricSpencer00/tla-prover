---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half

VARIABLES p

vars == << p >>

TypeOK ==
  /\ p \in [num : 1 .. 4, den : 1 .. 8]

Init ==
  /\ p = One

Next ==
  /\ p' = Half

Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Spec == Init /\ [][Next]_vars

NoDenZero == p.den # 0

HalfIsHalf == Half = [num |-> 1, den |-> 2]

Final ==
  /\ p = [num |-> 3, den |-> 8]
  /\ Norm(p) = [num |-> 3, den |-> 8]
====