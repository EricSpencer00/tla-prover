---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Dyadic rational numbers are represented as records with fields
\*   num : integer numerator
\*   den : positive integer denominator
\* The denominator is always a power of two after normalization.
\* ----------------------------------------------------------------------

CONSTANTS
\* No external constants are required.

\* ----------------------------------------------------------------------
\* Record constructor examples (provided for reference)
\* ----------------------------------------------------------------------
\* [num |-> 1, den |-> 1]
\* [num |-> p.num, den |-> p.den * 2]
\* [num |-> p.num \div 2, den |-> p.den \div 2]

\* ----------------------------------------------------------------------
\* Definition of the value one (the dyadic rational 1/1)
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

\* ----------------------------------------------------------------------
\* Halving operator: multiplies the denominator by 2, leaving the
\* numerator unchanged.
\* ----------------------------------------------------------------------
Half(p) == [num |-> p.num, den |-> p.den * 2]

\* ----------------------------------------------------------------------
\* Recursive normalization operator.  While both numerator and denominator
\* are even, divide each by 2.  The result is a dyadic rational in which at
\* least one of the components is odd (or the denominator is 1).
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)

Norm(p) ==
  IF (p.num % 2 = 0) /\ (p.den % 2 = 0)
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Helper predicate stating that a record is a well‑formed dyadic rational.
\* The denominator must be a positive integer (Nat) and after normalization
\* at least one of num or den is odd.
\* ----------------------------------------------------------------------
IsDyadic(p) ==
  /\ p \in [num : Int, den : Nat]
  /\ p.den > 0
  /\ LET q == Norm(p) IN
       (q.num % 2 # 0) \/ (q.den % 2 # 0)

\* ----------------------------------------------------------------------
\* The set of all dyadic rationals.
\* ----------------------------------------------------------------------
Dyadic == { p \in [num : Int, den : Nat] : IsDyadic(p) }

====