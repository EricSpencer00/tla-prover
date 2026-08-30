---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS vOne, vHalf

Operators == {"*", "\div", "%", "="}

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ p.den >= 1

Init ==
    /\ p = [num |-> 1, den |-> 1]

Next ==
    /\ p' \in {[num |-> p.num, den |-> p.den * 2],
                [num |-> p.num * 2, den |-> p.den]}
    \/ p' = IF p.num % 2 = 0 /\ p.den % 2 = 0
            THEN [num |-> p.num \div 2, den |-> p.den \div 2]
            ELSE p

Spec == Init /\ [][Next]_vars

InRange ==
    /\ p.num >= 0
    /\ p.den >= 1
    /\ p.den <= 4

ValueOne ==
    /\ p.num = vOne
    /\ p.den = vHalf

Halving ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]
    /\ p' # p

====