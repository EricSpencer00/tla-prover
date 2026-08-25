---- MODULE DyadicRationals ----
EXTENDS Integers

\* Dyadic rational numbers are represented as records with integer numerator
\* and positive integer denominator.
Dyadic == [num : Int, den : Nat]

\* The dyadic rational representing the value one.
One == [num |-> 1, den |-> 1]

\* Halving operator: multiplies the denominator by two.
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Normalization operator: repeatedly divides numerator and denominator by two
\* while both are even.
RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
        THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
        ELSE p

\* Placeholder operators required by the .cfg (no specific behavior demanded).
SPECIFICATION == One
INIT == One
NEXT == FALSE
INVARIANTS == TRUE
PROPERTIES == TRUE

====