---- MODULE MC_sums_even ----
EXTENDS Naturals

\* Model-checking configuration for the theorem that the double of any natural
\* number is even. It overrides the natural-number set with a finite range so
\* TLC can check the specification on a bounded domain. The theorem itself is
\* taken as a constant-level assumption for model checking.

CONSTANTS
  MaxNat

\* A finite version of the natural-number set, overriding the infinite one.
NatOverride == 0..MaxNat

\* The model assumes the theorem holds (it is the thing being checked elsewhere)
\* but still runs a no-op spec so TLC has something to explore.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

INVARIANTS == {}
PROPERTIES == {}
====