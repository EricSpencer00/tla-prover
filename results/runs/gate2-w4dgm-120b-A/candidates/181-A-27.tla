---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the unbounded Nat from Naturals with a finite range.
\* It is defined here (not declared) so Nat from Naturals is overridden as
\* required by the config; the set has to stay finite for TLC to check.
NatOverride == 0..MaxNat

Spec == INSTANCE SumEven

Init == INSTANCE SumEven.Init

Next == INSTANCE SumEven.Next

TypeOK == INSTANCE SumEven.TypeOK

\* The theorem is assumed as a constant-level fact for model checking.
EvenDoubleIsEven == INSTANCE SumEven.EvenDoubleIsEven
====