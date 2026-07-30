---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

ASSUME Value \in SUBSET (0 .. 9)

VARIABLES candidate, count, i, seq, winner

vars == <<candidate, count, i, seq, winner>>

TypeOK ==
  /\ candidate \in Value
  /\ count \in 0 .. 3
  /\ i \in 0 .. 3
  /\ seq \in [0 .. 2 -> Value]
  /\ winner \in Value \cup {"none"}

\* The candidate always reflects the current state of the scan.
Inv ==
  /\ candidate \in Value
  /\ count >= 0
  /\ i = 0 \/ candidate = seq[i - 1] \/ \A j \in 0 .. i - 1 : seq[j] # candidate

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ i = 0
  /\ \E s \in [0 .. 2 -> Value] : seq = s
  /\ winner = "none"

Step ==
  /\ i < 3
  /\ IF count = 0
       THEN candidate' = seq[i]
       ELSE IF candidate = seq[i]
              THEN candidate' = candidate
              ELSE candidate' = candidate
  /\ IF count = 0 \/ candidate = seq[i]
       THEN count' = count + 1
       ELSE count' = count - 1
  /\ i' = i + 1
  /\ UNCHANGED <<seq, winner>>

Finish ==
  /\ i = 3
  /\ winner' = IF count = 0 THEN "none" ELSE candidate
  /\ UNCHANGED <<candidate, count, i, seq>>

Next == Step \/ Finish

Spec == Init /\ [][Next]_vars

\* First invariant: the declared type signature is never broken.
TypeOK == TypeOK

\* Second invariant: after scanning the whole sequence the candidate is
\* exactly the only value that can appear in a strict majority of positions.
Correct ==
  /\ i = 3
  /\ \A x \in Value :
       (2 * Cardinality({k \in 0 .. 2 : seq[k] = x}) > 3) => x = winner

====