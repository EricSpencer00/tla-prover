---- MODULE MC_sums_even ----
EXTENDS Naturals

\* The bounded model replaces the infinite natural-number set with a
\* finite range so TLC can explore every value concretely.  The theorem
\* itself is lifted as a constant-level assumption rather than re-proved.
CONSTANTS
  MaxNat
  Nat

ASSUME Nat = 0 .. MaxNat

VARIABLES
  n

vars == << n >>

TypeOK ==
  /\ n \in Nat

Init ==
  /\ n = 0

Next ==
  /\ n < MaxNat
  /\ n' = n + 1

Spec ==
  /\ Init
  /\ [][Next]_vars

\* The theorem from the base spec, assumed here as a constant-level fact.
TheoremAssumption ==
  \A x \in Nat : (2 * x) % 2 = 0

Terminating ==
  n = MaxNat

====