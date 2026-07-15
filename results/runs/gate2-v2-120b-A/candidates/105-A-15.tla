---- MODULE DyadicRationals ----
EXTENDS Integers, TLC

\* ----------------------------------------------------------------------
\* Constants (none are required by the .cfg, but we declare the names
\* used in the description as CONSTANT-like operators for readability)
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: adds a factor of two to the denominator.
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Recursive normalization operator.
\* It removes a common factor of two from numerator and denominator.
\* ----------------------------------------------------------------------
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* State variable representing the current dyadic rational.
\* ----------------------------------------------------------------------
VARIABLE p

\* ----------------------------------------------------------------------
\* Type predicate (helps TLC, not required by the description but harmless)
\* ----------------------------------------------------------------------
Dyadic == { [num |-> n, den |-> d] :
               n \in Nat /\ d \in Nat /\ d > 0 }

\* ----------------------------------------------------------------------
\* Initial state: start with the value one.
\* ----------------------------------------------------------------------
Init == p = One

\* ----------------------------------------------------------------------
\* Next-state relation: either halve the current value or normalize it.
\* ----------------------------------------------------------------------
Next ==
  \/ p' = Half(p)
  \/ p' = Norm(p)

\* ----------------------------------------------------------------------
\* Specification name required by the task.
\* ----------------------------------------------------------------------
Specification == Init /\ [][Next]_<<p>>

\* ----------------------------------------------------------------------
\* The module does not require any additional identifiers, but the names
\* above (One, Half, Norm, Init, Next, Specification) exactly match those
\* mentioned in the natural‑language description.
\* ----------------------------------------------------------------------
====