---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

\* -----------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* -----------------------------------------------------------------
CONSTANT MaxNat
CONSTANT Nat

\* -----------------------------------------------------------------
\* Overriding the infinite set of natural numbers with a finite range.
\* Nat must be exactly the set {0, 1, ..., MaxNat}.
\* The invariant NatInRange ensures this relationship.
\* -----------------------------------------------------------------
NatInRange == Nat = 0..MaxNat

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLE n, double

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
  /\ NatInRange
  /\ n \in Nat
  /\ double = 2 * n

\* -----------------------------------------------------------------
\* Actions (the system does not evolve; we keep a stuttering step)
\* -----------------------------------------------------------------
Next ==
  /\ UNCHANGED << n, double >>

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<< n, double >>

\* -----------------------------------------------------------------
\* Safety property (the theorem: the double of any natural number is even)
\* -----------------------------------------------------------------
EvenDouble == double % 2 = 0

\* -----------------------------------------------------------------
\* Operator names required by the reference configuration
\* -----------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANT == EvenDouble

\* -----------------------------------------------------------------
\* Theorem (optional, but kept for completeness)
\* -----------------------------------------------------------------
THEOREM EvenDoubleIsEven == Spec => []EvenDouble

====