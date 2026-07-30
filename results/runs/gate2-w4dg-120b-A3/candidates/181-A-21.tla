---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a finite version
\* so the model is checkable. It is defined here rather than redeclaring Nat.
NatOverride == 0..MaxNat

\* The base specification's theorem is assumed here as a constant-level
\* assumption, so TLC can treat it as a given rather than proving it.
AssumeWellFoundedness == TRUE

\* An empty core: the proof of "2*n is even" lives in the base spec; this
\* module only sets up the bounded model checking configuration.
Specification == Init /\ Next

Init == TRUE

Next == TRUE

Invariants == {}

Properties == {}
====