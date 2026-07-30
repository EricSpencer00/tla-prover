---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, cand, cnt, i

vars == <<seq, cand, cnt, i>>

TypeOK ==
  /\ seq \in [0..2 -> Value]
  /\ cand \in Value
  /\ cnt \in Nat
  /\ i \in 0..4

Init ==
  /\ seq = [k \in 0..2 |-> "v1"]
  /\ cand = "v1"
  /\ cnt = 0
  /\ i = 0

Vote ==
  /\ i < 4
  /\ LET x == seq[i] IN
       /\ cand' = IF cnt = 0 THEN x ELSE cand
       /\ cnt' = IF cnt = 0 THEN 1 ELSE IF x = cand THEN cnt + 1 ELSE cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Vote]_vars

Inv ==
  /\ i >= 1
  /\ (i - (cnt - 1)) / 2 <= cnt
  /\ cnt <= i

Correct ==
  /\ i >= 1
  /\ (\A j \in 0..(i - 1) : seq[j] = cand) => i >= 2
  /\ (\A j \in 0..(i - 1) : (2 * Cardinality({k \in 0..(i - 1) : seq[k] = seq[j]})) > i) => seq[j] = cand

PROPERTIES == Correct

Spec == Spec

====