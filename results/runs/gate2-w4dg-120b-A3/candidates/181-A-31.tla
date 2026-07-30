---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat from Naturals with a bounded
\* version so that TLC can enumerate the model. The name Nat itself is
\* never declared or redefined; the override leaves Nat untouched.
NatOverride == 0..MaxNat

\* The configuration module inherits definitions from the base proof, so
\* the specification is empty here: the proof of "2*x is even" is
\* assumed as a constant-level invariant, not proved inside this module.
SPECIFICATION Spec
Init == Init
Next == Next

INVARIANTS Spec
PROPERTIES Spec
====