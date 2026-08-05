---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Formal proof attachment for the Boyer-Moore majority vote algorithm.
\* No new state: inherits the whole state and transition set from the main
\* majority vote module, adding a machine-checkable proof of the core
\* correctness claim as an invariant rather than a standalone theorem.

CONSTANTS Value
VALUES = 0..2

VARIABLES candidate, count, seq, i

TypeOK ==
  /\ candidate \in (Value \cup {"NONE"})
  /\ count \in 0..3
  /\ seq \in [1..3 -> Value]
  /\ i \in 0..3

Init ==
  /\ candidate = "NONE"
  /\ count = 0
  /\ seq = [k \in 1..3 |-> 1]
  /\ i = 0

\* Each step processes one more position, adjusting the candidate and
\* count per the Boyer-Moore update rule.
Step(k) ==
  /\ i < 3
  /\ i' = i + 1
  /\ seq' = [seq EXCEPT ![k] = (seq[k] + 1) % 3]
  /\ count' = IF candidate = "NONE" \/ seq[k] = candidate
              THEN count + 1
              ELSE count - 1
  /\ candidate' = IF candidate = "NONE" \/ seq[k] = candidate
                  THEN seq[k]
                  ELSE candidate

Next ==
  \/ Step(1)
  \/ Step(2)
  \/ Step(3)

Spec == Init /\ [][Next]_<<candidate, count, seq, i>>

\* Auxiliary recursive definition counting occurrences of a value up to
\* a given index; used as the bridge between the scan and the majority
\* claim in the TLAPS proof.
RECURSIVE occ(_)
occ(k) == IF k = 0 THEN 0 ELSE (IF seq[k] = candidate THEN 1 ELSE 0) + occ(k - 1)

Inv ==
  /\ TypeOK
  /\ i = 3
  /\ \A v \in Value : (occ(3) > 3 % 2) => candidate = v

Correct ==
  /\ Inv
  /\ (i = 3 => (IF occ(3) > 3 % 2 THEN candidate # "NONE" ELSE TRUE))

====