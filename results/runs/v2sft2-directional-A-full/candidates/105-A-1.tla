---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
    One
    Half

VARIABLES
    s       \* the current state, a record with fields num and den

\* Record constructor helpers
Num(p) == p.num
Den(p) == p.den

\* The Halving operator: given a state p, return a new state with both fields halved
Half(p) == [num |-> p.num \div 2, den |-> p.den \div 2]

\* The Norm operator: recursively reduce a state by halving while both fields are even
Norm(p) ==
    IF (p.num % 2 = 0) /\ (p.den % 2 = 0) THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE
        p

\* Initial state: the rational number one, namely 1/1
Init == s = [num |-> 1, den |-> 1]

\* Next-state relation: either leave the state unchanged (stutter) or apply Half
Next ==
    \/ s' = s
    \/ s' = Half(s)

=============================================================================