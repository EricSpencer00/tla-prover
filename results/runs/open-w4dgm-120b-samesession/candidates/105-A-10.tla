---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, EqualityOps, ExtendsModules, Specification, id

OperatorDefNames == {"One", "Half", "Norm"}

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ p.den >= 1

Init ==
    /\ p = [num |-> 1, den |-> 1]

One ==
    p

Half ==
    [num |-> p.num, den |-> p.den * 2]

Norm(r) ==
    IF r.num % 2 = 0 /\ r.den % 2 = 0 THEN Norm([num |-> r.num \div 2, den |-> r.den \div 2]) ELSE r

Next ==
    \/ p' = One
    \/ p' = Half
    \/ p' = Norm(p)

Spec ==
    /\ Init
    /\ [][Next]_vars

Invariant == TRUE

Property == TRUE

====