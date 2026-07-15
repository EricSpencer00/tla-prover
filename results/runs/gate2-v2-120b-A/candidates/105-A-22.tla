---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANT One, Half

\* -----------------------------------------------------------------
\* Dyadic rational record definition
\* -----------------------------------------------------------------
VARIABLE p

\* -----------------------------------------------------------------
\* Helper: check if a number is even
\* -----------------------------------------------------------------
Even(n) == n % 2 = 0

\* -----------------------------------------------------------------
\* Normalization operator: repeatedly divide numerator and denominator
\* by two while both are even.
\* -----------------------------------------------------------------
Norm(q) == 
    IF Even(q.num) /\ Even(q.den) 
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

\* -----------------------------------------------------------------
\* Initialization: start with the dyadic rational 1/1
\* -----------------------------------------------------------------
Init == 
    p = [num |-> 1, den |-> 1] /\ 
    p = Norm(p)

\* -----------------------------------------------------------------
\* Halving operator: doubles the denominator
\* -----------------------------------------------------------------
HalfOp == 
    p' = Norm([num |-> p.num, den |-> p.den * 2])

\* -----------------------------------------------------------------
\* Next-state relation: only halving is allowed
\* -----------------------------------------------------------------
Next == HalfOp

\* -----------------------------------------------------------------
\* Specification (for TLC)
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<p>>

\* -----------------------------------------------------------------
\* Safety invariant: after normalization numerator is odd or denominator is odd
\* (i.e., they cannot both be even)
\* -----------------------------------------------------------------
Safe == ~ (Even(p.num) /\ Even(p.den))

\* -----------------------------------------------------------------
\* No additional properties required
\* -----------------------------------------------------------------
====