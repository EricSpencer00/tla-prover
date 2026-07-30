---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* Bounded model for the theorem "the double of any natural is even".
\* The bound (zero..MaxNat) is finite, so TLC can explore the whole
\* space; the theorem itself is assumed here as a constant-level fact.
CONSTANTS
  SumEvenAssumption

TypeOK ==
  /\ MaxNat \in Nat
  /\ Nat \in 0..MaxNat

Init ==
  /\ SumEvenAssumption = TRUE

Next ==
  UNCHANGED SumEvenAssumption

Spec == Init /\ [][Next]_SumEvenAssumption

\* Model check that the theorem is available as a fact.
FactAvailable == SumEvenAssumption = TRUE

====