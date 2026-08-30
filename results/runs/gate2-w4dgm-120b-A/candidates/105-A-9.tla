---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
EqualityOps == {"="}
Records == {"[num |-> p.num \\div 2, den |-> p.den \\div 2]"}

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Spec == 1

TypeOK ==
    /\ p \in [num : Int, den : Int]
    /\ p.den # 0

Init ==
    /\ p = One

HalfOp ==
    / p' = Half
    /\ UNCHANGED vars

NormStep ==
    /\ p.num % 2 = 0 /\ p.den % 2 = 0
    /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    /\ UNCHANGED vars

Next == HalfOp \/ NormStep

SpecOk == Spec = 1

====