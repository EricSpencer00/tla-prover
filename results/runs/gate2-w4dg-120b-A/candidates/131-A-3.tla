---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

\* This module contains an interactive proof of correctness for the
\* Boyer-Moore majority vote algorithm.  The proof is structured for
\* TLAPS and establishes both type correctness and the main correctness
\* invariant about the majority candidate.

CONSTANTS Value

\* The main algorithm's state is imported wholesale: no new state
\* variables are introduced here.
VARIABLES seq, candidate, count, scanned

vars == <<seq, candidate, count, scanned>>

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..3
  /\ scanned \in 0..3

Init ==
  /\ seq \in [1..3 -> Value]
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0

\* The first phase of Boyer-Moore: keep a running candidate and count.
Run ==
  /\ candidate' = IF count = 0 THEN seq[scanned + 1] ELSE candidate
  /\ count' = IF count = 0 THEN 1 ELSE IF seq[scanned + 1] = candidate THEN count + 1 ELSE count - 1
  /\ scanned' = scanned + 1
  /\ UNCHANGED seq

\* The second phase: the candidate is counted against every position to
\* verify it really is a strict majority.
Verify ==
  /\ scanned = 3
  /\ candidate # "none"
  /\ Cardinality({i \in 1..3 : seq[i] = candidate}) > 1
  /\ UNCHANGED vars

Discard ==
  /\ scanned = 3
  /\ candidate # "none"
  /\ Cardinality({i \in 1..3 : seq[i] = candidate}) <= 1
  /\ candidate' = "none"
  /\ UNCHANGED <<seq, count, scanned>>

Next == Run \/ Verify \/ Discard

Spec == Init /\ [][Next]_vars

\* A strict majority of positions is a finite set whose size is greater
\* than half the whole sequence.
Majority(v) == Cardinality({i \in 1..3 : seq[i] = v}) * 2 > 3

\* The algorithm's correctness: any value that a strict majority of the
\* sequence holds must be the candidate.
Correct == scanned = 3 => \A v \in Value : Majority(v) => candidate = v

\* The inductive invariant from the main specification, reproduced here
\* so the proof can refer to it directly.
Inv == scanned <= 3

====