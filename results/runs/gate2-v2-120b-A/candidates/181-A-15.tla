---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS MaxNat, Nat

\* ----------------------------------------------------------------------
\* Override the infinite natural number set with a finite range.
\* This is enforced as a constant-level assumption in the .cfg file.
\* ----------------------------------------------------------------------
Nat == 0..MaxNat

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLE x

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == /\ x \in Nat
        /\ x = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Inc == /\ x \in Nat
      /\ x < MaxNat
      /\ x' = x + 1

\* (No other actions; the system may also stutter)
Next == Inc \/ UNCHANGED x

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Safety invariant: the invariant that should hold in every reachable state.
\* It expresses that the double of the current natural number is even.
\* ----------------------------------------------------------------------
Inv_EvenDouble == (2 * x) % 2 = 0

\* ----------------------------------------------------------------------
\* Theorem from the base specification (assumed true for model checking)
\* ----------------------------------------------------------------------
THEOREM DoubleEven == \A n \in Nat : (2 * n) % 2 = 0

\* ----------------------------------------------------------------------
\* Operators required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANT     == Inv_EvenDouble
PROPERTIES    == DoubleEven

====