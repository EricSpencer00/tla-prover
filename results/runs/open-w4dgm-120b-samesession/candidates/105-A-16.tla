---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

None == [num |-> 1, den |-> 1]

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES p

vars == <<p>>

Init == p = None

Halve == p' = [num |-> p.num, den |-> p.den * 2]

Normalize == p' = Norm(p)

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

OnlyRationals == p.den # 0 /\ p.den = 2 ^ (INT(LOG2(p.den)))

RationalUsed == p.num * 2 <= 2 ^ id

EndOfFirstHalf == p.num = 0

====