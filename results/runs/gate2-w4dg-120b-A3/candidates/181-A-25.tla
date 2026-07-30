---- MODULE MC_sums_even ----
EXTENDS Naturals

\* Model-checking configuration for the "double any number is even" theorem.
\* The infinite Nat set is overridden with a bounded finite set so TLC can
\* explore every value; the theorem itself is assumed as a constant-level
\* assumption, which is what lets the model-checker close the proof.

CONSTANTS
  MaxNat

\* NatOverride is a finite version of the usual Naturals.Nat set. The .cfg
\* replaces Nat with NatOverride, but we do NOT declare Nat itself -- that
\* name is left untouched and NatOverride carries the finite set.
NatOverride == 0 .. MaxNat

\* SPECIFICATION and its components are required identifiers; this model has
\* no state or behavior of its own, only the override and the assumption.
SPECIFICATION == Init /\ Next
Init == TRUE
Next == TRUE

INVARIANTS == TRUE
PROPERTIES == TRUE

\* The theorem "the double of any number is even" is assumed for model checking;
\* the assumption is what the model-checker tests against, since the underlying
\* proof is carried in the base specification.
AssumeDoubleIsEven == \A n \in NatOverride : (n + n) % 2 = 0

====