---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

Zero == 0

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES forks, car

vars == <<forks, car>>

TypeOK ==
  /\ forks \in 0..3
  /\ car \in [a: {"A", "B", "C"}, pos: {"ns", "ew"}]

Init ==
  /\ forks = 3
  /\ car = [a |-> "A", pos |-> "ns"]

Take ==
  /\ forks > 0
  /\ forks' = forks - 1
  /\ UNCHANGED car

Enter ==
  /\ car' = [a |-> car.a, pos |-> IF car.pos = "ns" THEN "ew" ELSE "ns"]
  /\ UNCHANGED forks

Leave ==
  /\ forks < 3
  /\ forks' = forks + 1
  /\ UNCHANGED car

Next == Take \/ Enter \/ Leave

Spec == Init /\ [][Next]_vars

ForkConservation == forks = 3 - (IF car.a # "A" /\ car.pos # "ns" THEN 1 ELSE 0)

====