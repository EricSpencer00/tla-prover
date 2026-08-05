---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* An override of the built-in `Nat` set from the Naturals module: this finite
\* version of the naturals is what makes the double-even theorem checkable
\* by TLC.  It must be assigned in the .cfg (here the range 0..MaxNat) and
\* it replaces the imported `Nat` name, so we keep EXTENDS Naturals but do
\* not redeclare Nat itself.
NatOverride == 0..MaxNat

\* Nothing to define beyond the override: the theorem (forall n \in Nat : 2*n is even)
\* lives in the base specification, and this module's job is only to
\* constrain the domain so TLC can explore it.

THISMODULE == "MC_sums_even"
====