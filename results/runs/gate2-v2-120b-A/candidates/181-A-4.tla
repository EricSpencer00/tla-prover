---- MODULE MC_sums_even ----
EXTENDS Naturals

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\*   MaxNat : the largest natural number in the finite domain
\*   Nat    : the finite set of natural numbers, overridden in the cfg
\* ----------------------------------------------------------------------
CONSTANTS MaxNat, Nat

\* ----------------------------------------------------------------------
\* Variables
\*   x : a natural number from the finite set Nat
\* ----------------------------------------------------------------------
VARIABLE x

\* ----------------------------------------------------------------------
\* Initialization
\*   x is chosen nondeterministically from Nat
\* ----------------------------------------------------------------------
Init ==
    x \in Nat

\* ----------------------------------------------------------------------
\* Action
\*   x may change to any other value in Nat
\*   (the actual logic of the original proof is captured by the invariant)
\* ----------------------------------------------------------------------
Next ==
    x' \in Nat

\* ----------------------------------------------------------------------
\* Safety property (invariant)
\*   The double of x is even
\* ----------------------------------------------------------------------
EvenDouble ==
    (2 * x) % 2 = 0

\* ----------------------------------------------------------------------
\* Specification (required name for TLC)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT EvenDouble
PROPERTIES EvenDouble

====