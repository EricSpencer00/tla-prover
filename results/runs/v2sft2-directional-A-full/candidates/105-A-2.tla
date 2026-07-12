---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS

\* No constants are required by the configuration

\* --- Primitive values ---
One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

\* --- Normalization operator (recursive) ---
Norm(p) ==
    IF (p.num % 2 = 0) /\ (p.den % 2 = 0) THEN
        Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE
        p

\* --- Example usage of the record constructor for halving ---
Halve(p) == [num |-> p.num, den |-> p.den * 2]

\* --- Example usage of the record constructor for reduction (used inside Norm) ---
Reduce(p) == [num |-> p.num \div 2, den |-> p.den \div 2]

\* --- Specification section (empty as no state dynamics are defined) ---
VARIABLES {}

Init == /\ TRUE
Next == /\ TRUE

Spec == Init /\ [][Next]_<<>>

====