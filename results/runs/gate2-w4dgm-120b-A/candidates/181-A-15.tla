---- MODULE MC_sums_even ----
\* Model-checking configuration for the "double of any natural number is even" proof.
\* It extends the base proof spec and overrides Nat with a finite range so TLC can
\* explore a bounded state space.
EXTENDS Naturals

CONSTANTS MaxNat

\* Nat is replaced by a finite version so the model is checkable (MaxNat bounded).
NatOverride == 0..MaxNat
\* Theorem from the base spec, assumed as a constant-level fact for model checking.
DoubleEven(n) == (2 * n) % 2 = 0

\* The config file fires SPECIFICATION, INIT, NEXT, INVARIANTS and PROPERTIES on
\* this module, so each of them must be defined here exactly.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

\* The config file would also override the Nat definition with NatOverride, binding
\* Nat to the finite set 0..MaxNat, but that override is external to the module.
====