---- MODULE DyadicRationals ----
EXTENDS Naturals, Integers, Sequences

\* ----------------------------------------------------------------------
\* Record definition for a dyadic rational: two integer components,
\* numerator (num) and denominator (den).  The denominator is always
\* strictly positive.
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Constants representing special dyadic rationals.
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
Even(n) == n % 2 = 0

\* ----------------------------------------------------------------------
\* Normalization operator: repeatedly divide numerator and denominator
\* by 2 while both are even.  The recursion is expressed with a WHILE loop.
\* ----------------------------------------------------------------------
Norm(q) == 
  LET 
    rec(x) == 
      IF Even(x.num) /\ Even(x.den) 
        THEN rec([num |-> x.num \div 2, den |-> x.den \div 2])
        ELSE x
  IN rec(q)

\* ----------------------------------------------------------------------
\* The initial state: start with the dyadic rational 1/1.
\* ----------------------------------------------------------------------
Init == p = One

\* ----------------------------------------------------------------------
\* The only possible step: replace p by its normalized halved value.
\* The step implements the description:
\*   IF both components of p are even THEN divide both by 2,
\*   else leave p unchanged.  Afterwards, apply Norm to the result.
\* ----------------------------------------------------------------------
Next == 
  \/ 
    /\ p' = Norm([num |-> p.num, den |-> p.den * 2])   \* explicit “do nothing” step after
    /\ p'.den > 0                                      \* a sanity check
  \/
    /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    /\ Even(p.num) /\ Even(p.den)

\* ----------------------------------------------------------------------
\* The specification: safety closure of Init and Next.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<p>>

\* ----------------------------------------------------------------------
\* Optional (not required by the .cfg) but useful invariants.
\* ----------------------------------------------------------------------
InvDenPos == p.den > 0
InvNorm == p = Norm(p)

\* ----------------------------------------------------------------------
\* The THEOREM links the specification to the identifier expected by TLC.
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec

====