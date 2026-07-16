---- MODULE MCBoulanger ----
EXTENDS Boulanger

\* Declare a constant that represents the upper bound for the overridden natural numbers.
CONSTANT MaxNat

\* Ensure that MaxNat is not a standard natural number, so the overridden interval can be
\* distinguished from the built‑in Nat set.
ASSUME MaxNat \notin Nat

\* The overridden natural numbers range from 0 up to MaxNat (inclusive).
NatOverride == 0 .. MaxNat

\* State constraint: every process must keep its counter strictly below MaxNat.
\* This is a typical safety condition that must hold in every reachable state.
StateConstraint == \A process \in Procs : num[process] < MaxNat

====