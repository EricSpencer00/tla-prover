---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, EqualityOps, ArithmeticOps, ExtendsModules

Operators == {"One", "Half", "Norm"}
Rationals == {r \in [num : Nat, den : Nat] : r.den >= 1}

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

Step == p' = Half

Next == Step

Spec == Init /\ [][Step]_vars

ValueInvariant == p.num >= 1 /\ p.den >= 1

NormalizationProperty == p' = Norm(p)

====