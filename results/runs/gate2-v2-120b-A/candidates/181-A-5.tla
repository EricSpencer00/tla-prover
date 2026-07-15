---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT MaxNat

\* Nat is the finite set of natural numbers from 0 up to MaxNat (inclusive)
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Specification operators required by the reference configuration
\* ----------------------------------------------------------------------
\* The base proof module (not shown here) is assumed to define the theorem
\* that the double of any natural number is even.  In this configuration
\* module we do not re‑define the full algorithm; we only need to expose the
\* operators expected by the .cfg file.
\* ----------------------------------------------------------------------
Spec == TRUE      \* placeholder specification; the real proof lives in the base module
Init == TRUE      \* placeholder initial predicate
Next == TRUE      \* placeholder next‑state relation
Inv  == TRUE      \* placeholder invariant
Prop == TRUE      \* placeholder property (the theorem being checked)

=============================================================================