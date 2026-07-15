---- MODULE MC_sums_even ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxNat
CONSTANT Nat

\* -----------------------------------------------------------------------------
\* Nat is overridden to be the finite set {0, 1, ..., MaxNat}
\* This constant will be assigned in the .cfg file.
\* -----------------------------------------------------------------------------

VARIABLE x

\* ---------- Initialization ----------
Init == 
    /\ x \in Nat

\* ---------- Actions ----------
\* Doubling any natural number should produce an even result.
\* We model the action as a nondeterministic step that picks a number y from Nat
\* and asserts that its double is even. The step does not change any state.
DoubleEven ==
    \E y \in Nat :
        (2 * y) % 2 = 0

\* The system can stutter (do nothing) as well.
Next == 
    \/ DoubleEven
    \/ UNCHANGED x

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<x>>

\* ---------- Safety property ----------
\* The theorem from the base proof: for every natural number y in Nat,
\* its double is even.
AllDoublesEven == \A y \in Nat : (2 * y) % 2 = 0

\* ---------- Liveness and other properties ----------
\* No liveness property is required for this model.
LivenessProp == TRUE

\* ---------- Invariant ----------
\* A trivial invariant that always holds; the real property is the theorem above.
TrivialInv == x = x

=============================================================================