---- MODULE DyadicRationals ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (defined as operators for use in the specification)
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization operator:
\*   While both numerator and denominator are even, divide each by 2.
\*   Otherwise, return the record unchanged.
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES current

\* ----------------------------------------------------------------------
\* Type predicate (optional but useful for TLC)
\* ----------------------------------------------------------------------
Dyadic == { [num |-> n, den |-> d] :
              n \in Nat /\ d \in Nat /\ d > 0 }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ current = One
  /\ current \in Dyadic

\* ----------------------------------------------------------------------
\* Next-state relation
\*   - Halve the current dyadic rational.
\*   - Or normalize the current dyadic rational.
\* Both actions keep the state within Dyadic.
\* ----------------------------------------------------------------------
Halve ==
  /\ current' = Half(current)
  /\ current' \in Dyadic

Normalize ==
  /\ current' = Norm(current)
  /\ current' \in Dyadic

Next ==
  \/ Halve
  \/ Normalize

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<current>>

\* ----------------------------------------------------------------------
\* Optional invariant (states all values are dyadic)
\* ----------------------------------------------------------------------
DyadicInv == current \in Dyadic

\* ----------------------------------------------------------------------
\* Optional property: the value of the rational number represented by
\* (num/den) is always in the interval (0, 1].
\* ----------------------------------------------------------------------
Value(x) == x.num / x.den

Prop == \A p \in Dyadic : 0 < Value(p) /\ Value(p) <= 1

====