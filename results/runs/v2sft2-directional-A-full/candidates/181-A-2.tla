---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS MaxNat, Nat

\* ----------------------------------------------------------------------
\* Override the natural number set with a bounded finite range
\* ----------------------------------------------------------------------
\* The constant MaxNat will be bound in the configuration (e.g., 1000000).
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* The base specification (from the main proof module) is assumed to be
\* imported as a whole. It defines the safety theorem stating that
\* the double of any natural number is even. We do not reimplement that
\* theorem here; instead we rely on the imported definitions.
\* ----------------------------------------------------------------------
\* (In a full model, the base spec would be imported with the same name.)
\* For this isolated module, we declare the common definitions that the
\* theorem will use so that TLC can evaluate them.
\* ----------------------------------------------------------------------
Even(n) == n % 2 = 0

Double(n) == 2 * n

\* ----------------------------------------------------------------------
\* Safety property: the double of any natural number in Nat is even.
\* This is the invariant we expect to hold in all reachable states.
\* ----------------------------------------------------------------------
SumsEven == \A n \in Nat : Even(Double(n))

\* ----------------------------------------------------------------------
\* Because there are no state variables or actions, the specification
\* consists solely of the invariant that must be preserved.
\* ----------------------------------------------------------------------
SPECIFICATION SumsEven

\* ----------------------------------------------------------------------
\* To make the specification type-checkable, we provide minimal
\* definitions for INIT and NEXT that leave the state unchanged.
\* ----------------------------------------------------------------------
VARIABLES \* No state variables

INIT == UNCHANGED << >>

NEXT == UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Invariant used by TLC (the same as the safety property)
\* ----------------------------------------------------------------------
INVARIANT SumsEven

\* ----------------------------------------------------------------------
\* Placeholder for any additional properties (none in this case)
\* ----------------------------------------------------------------------
\* No Liveness properties are required for this safety theorem.

====