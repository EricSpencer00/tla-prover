---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

Halve == p' = Half

NormStep == p' = Norm(p)

Next == Halve \/ NormStep

Spec == Init /\ [][Next]_vars

RECURSIVE QEq(_, _)
QEq(q1, q2) ==
  IF q1 = q2 THEN TRUE
  ELSE IF q1.den # q2.den THEN FALSE
  ELSE q1.num = q2.num

SpecOK == QEq(p, One)

StateBound == p.den <= 16 \/ p.num <= 16

====