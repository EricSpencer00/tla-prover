---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication,
  IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

Operators == {"+", "-"}

VARIABLES p

vars == <<p>>

Init ==
  /\ p = [num |-> 1, den |-> 1]

Double ==
  /\ p' = [num |-> p.num, den |-> p.den * 2]

Halve ==
  /\ p' = IF p.den > 1 THEN [num |-> p.num, den |-> p.den \div 2] ELSE p

Multiply ==
  /\ \E k \in 1..2 : p' = [num |-> p.num * k, den |-> p.den]

Divide ==
  /\ p.den % 2 = 0
  /\ p' = [num |-> p.num, den |-> p.den \div 2]

Next == Double \/ Halve \/ Multiply \/ Divide

Spec == Init /\ [][Next]_vars

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

====