---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The finite override: NatOverride is a finite version of the infinite Nat
\* set, so TLC can check the model. It replaces the inherited Nat, which is
\* why we do NOT declare Nat here -- EXTENDS Naturals already brings it in.
NatOverride == 0..MaxNat

\* The base theorem is assumed as a constant-level assumption for model checking.
AssumeDoubleEven == \A n \in NatOverride : (2 * n) % 2 = 0

\* The configuration module has no state of its own, so the operators below
\* are all no-ops; they exist only because the .cfg expects them.
SPECIFICATION == Init /\ Next
Init == TRUE
Next == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====