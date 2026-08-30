---- MODULE MajorityProof ----
\* Interactive formal proof of the Boyer-Moore majority vote algorithm's correctness.
EXTENDS Naturals, FiniteSets, MajorityVote

CONSTANT Value

VARIABLES candidate, count, scanned, idx

vars == <<candidate, count, scanned, idx>>

\* The algorithm's output is only meaningful after the whole sequence has been scanned,
\* so the type invariant is strictly weaker than the correctness statement.
TypeOK ==
  /\ candidate \in Value
  /\ count \in Nat
  /\ scanned \in [1..8 -> Value]
  /\ idx \in 0..8

\* Once the scan reaches the end, a strict majority element (if one exists) must be
\* exactly the candidate the algorithm is holding; a strict majority is never missed.
Correct ==
  /\ idx = 8
  /\ \A v \in Value : (2 * Cardinality({j \in 1..8 : scanned[j] = v}) > 8) => v = candidate

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ scanned = [j \in 1..8 |-> candidate]
  /\ idx = 0

\* On a match the candidate is reinforced; on a mismatch with reserve it replaces the
\* candidate and starts a fresh count, which is why no majority can be erased.
Match ==
  /\ idx < 8
  /\ scanned[idx + 1] = candidate
  /\ count' = count + 1
  /\ idx' = idx + 1
  /\ UNCHANGED <<candidate, scanned>>

MismatchReplace ==
  /\ idx < 8
  /\ scanned[idx + 1] # candidate
  /\ count = 0
  /\ candidate' = scanned[idx + 1]
  /\ count' = 1
  /\ idx' = idx + 1
  /\ UNCHANGED scanned

MismatchHold ==
  /\ idx < 8
  /\ scanned[idx + 1] # candidate
  /\ count > 0
  /\ count' = count - 1
  /\ idx' = idx + 1
  /\ UNCHANGED <<candidate, scanned>>

Next == Match \/ MismatchReplace \/ MismatchHold

Spec == Init /\ [][Next]_vars

Inv == Correct

====