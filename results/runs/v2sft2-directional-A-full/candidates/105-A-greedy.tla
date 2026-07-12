---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS One, Half, Norm

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
\* A dyadic rational is represented as a record with integer fields num and den
DyadicRational == [num : Nat, den : Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The record constructor for the value one
One == [num |-> 1, den |-> 1]

\* The record constructor for halving a dyadic rational
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* The recursive normalization operator
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == x = One

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ x' = Half(x)          \* apply the halving operator
  \/ x' = Norm(x)          \* apply the normalization operator

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Theorems (optional, not required by the .cfg but useful for TLC)
\* ----------------------------------------------------------------------
\* The denominator is always a power of two
DenominatorPowerOfTwo ==
  \A p \in {x} : p.den \in {2^k : k \in Nat}

====