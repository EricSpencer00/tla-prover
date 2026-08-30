---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
EqualityOps == {"="}

CONSTANTS ArithmeticOps, EqualityOps

VARIABLES p, normCalls

vars == <<p, normCalls>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Spec == p' = [num |-> 1, den |-> 1] /\ normCalls' = 0

Init == Spec

ApplyHalf == p' = Half /\ normCalls' = normCalls

ApplyNorm == p' = Norm(p) /\ normCalls' = normCalls + 1

Next == Init \/ ApplyHalf \/ ApplyNorm

TypeOK == p \in [num : Int, den : Int]

DenominatorNotZero == p.den # 0

====