---- MODULE MC_sums_even ----
EXTENDS Integers, Naturals

\* Model-checking config module for the "double of any natural number is even"
\* proof.  It extends the main proof spec and overrides the Nat set with a
\* finite range so TLC can check the theorem for a bounded set of values.
\* The theorem itself is assumed here as a constant-level assumption.

CONSTANT MaxNat

\* NatOverride replaces the built-in infinite Nat so the model is checkable.
\* It must not be declared as a constant; it is defined as a finite set.
NatOverride == 0 .. MaxNat

\* The specification from the base proof, brought in for verification.  Its own
\* state (an abstract "value") is constrained by the finite NatOverride set.
SPECIFICATION == [value |-> 0]

\* The base proof's init sets the value to zero, which is always in range.
INIT == [value |-> 0]

\* The base proof's next step increments the value, wrapping at the bound so
\* all reachable states stay inside the finite NatOverride set.
NEXT == [value |-> IF @.value < MaxNat THEN @.value + 1 ELSE 0]

\* The invariant from the base proof: the double of any natural number is even.
INVARIANTS == "DoubleIsEven"

\* The theorem from the base proof, assumed constant-time here for model
\* checking.  It is not proved here -- this module's job is to enable TLC.
PROPERTIES == "DoubleIsEven"

====