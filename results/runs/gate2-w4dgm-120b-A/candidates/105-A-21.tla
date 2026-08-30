---- MODULE DyadicRationals ----
EXTENDS Integers

Operators == {"*", "\\div", "%"}
Comparisons == {"="}

VARIABLES p

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ p.den >= 1

Init ==
    /\ p = [num |-> 1, den |-> 1]

Half ==
    /\ p.den % 2 = 0
    /\ p' = [num |-> p.num, den |-> p.den * 2]

One ==
    /\ p' = [num |-> 1, den |-> 1]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

NormStep ==
    /\ (p.num % 2 = 0 /\ p.den % 2 = 0)
    /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])

Next ==
    \/ Half
    \/ One
    \/ NormStep

Spec == Init /\ [][Next]_p

DenPositive == p.den >= 1
====