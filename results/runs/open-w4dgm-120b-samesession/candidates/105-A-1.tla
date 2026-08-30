---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
Equality == {"="}

VARIABLES p

TypeOK ==
  /\ p \in [num : Int, den : Int]

Init ==
  /\ p = [num |-> 1, den |-> 1]

One ==
  [num |-> 1, den |-> 1]

Half ==
  [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
  THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
  ELSE q

Next ==
  /\ p' \in {One, Half, Norm(p)}
  /\ UNCHANGED << >>

Spec == Init /\ [][Next]_p

NoLossOfDenominator ==
  p.den # 0

EvenDenominatorHalves ==
  (p.den % 2 = 0) ~> (p.den % 2 = 1 \/ p.den = 1)

====