---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Type definitions (used only for documentation; no runtime effect)
\* ----------------------------------------------------------------------
Num == Integers
Den == Integers

\* ----------------------------------------------------------------------
\* Data structure: a dyadic rational is a record with fields num and den
\* ----------------------------------------------------------------------
\* A dyadic rational must have a positive denominator that is a power of two.
\* For simplicity, we allow zero numerator (representing 0).
\* ----------------------------------------------------------------------
Dyadic == [num : Num, den : Den]

\* ----------------------------------------------------------------------
\* The value ONE
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* The HALVING operator
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* The recursive normalisation operator
\* ----------------------------------------------------------------------
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

\* ----------------------------------------------------------------------
\* The state variable
\* ----------------------------------------------------------------------
VARIABLES Current

\* ----------------------------------------------------------------------
\* Initialization: start with the normalised value of ONE
\* ----------------------------------------------------------------------
Init ==
  Current = Norm(One)

\* ----------------------------------------------------------------------
\* Next-state relation: either halt (no change) or apply Half then Norm
\* ----------------------------------------------------------------------
Next ==
  \/ UNCHANGED Current
  \/ Current' = Norm(Half(Current))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Current>>

\* ----------------------------------------------------------------------
\* Safety invariant: Current is always a properly normalised dyadic rational
\* ----------------------------------------------------------------------
SafeInvariant ==
  /\ Current.den > 0
  /\ (Current.den = 1) \/ (Current.den % 2 = 0)
  /\ (Current.num = 0) \/ (Current.num % 2 = 1)

\* ----------------------------------------------------------------------
\* Optional: SAFETY PROPERTY names (used by TLC if specified in the .cfg)
\* ----------------------------------------------------------------------
SafeProperty == SafeInvariant

====