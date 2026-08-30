---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

VARIABLES seq, cand, idx, occ, seen

vars == <<seq, cand, idx, occ, seen>>

Init ==
  /\ seq \in [1..3 -> Value]
  /\ cand \notin Value
  /\ idx = 0
  /\ occ = 0
  /\ seen = {}

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ cand \in Value
  /\ idx \in 0..3
  /\ occ \in 0..3
  /\ seen \subseteq (1..3)

InitOk == TypeOK

Next ==
  \/ \E v \in Value, i \in 1..3 :
       /\ idx < 3
       /\ seq' = [seq EXCEPT ![i] = v]
       /\ cand' = v
       /\ idx' = idx + 1
       /\ occ' = IF (i \in seen) + (seq[i] = v) > 0 THEN occ + 1 ELSE occ
       /\ seen' = seen \cup {i}
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv ==
  /\ idx = 3
  /\ occ = Cardinality(seen)
  /\ (seen = 1..3 <=> idx = 3)

Correct ==
  /\ Inv
  /\ idx = 3
  /\ occ * 2 > 3
  => \A i \in 1..3 : seq[i] = cand

====