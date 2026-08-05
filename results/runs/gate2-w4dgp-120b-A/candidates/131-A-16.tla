---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm: a single running candidate and a
\* counter are scanned across the input sequence. The algorithm is correct:
\* if a value occurs in a strict majority of positions, that value is the
\* final candidate.

Seq == 1..3

VARIABLES candidate, count, scanned, majority

vars == <<candidate, count, scanned, majority>>

\* The set of positions before a given index.
Before(i) == { k \in 1..3 : k < i }

\* Positions where a value occurs before a given index.
Positions(v, i) == { k \in 1..3 : k < i /\ scanned[k] = v }

TypeOK ==
  /\ candidate \in Value
  /\ count \in 0..3
  /\ scanned \in [Seq -> Value]
  /\ majority \in {0} \cup Value

\* The main correctness invariant: if a value occurs in a strict majority
\* of the scanned prefix, it must be the running candidate.
Correct ==
  \A v \in Value :
    /\ (Cardinality({ k \in Seq : scanned[k] = v }) * 2 > 3) => candidate = v

Init ==
  /\ candidate \in Value
  /\ count = 0
  /\ scanned = [i \in Seq |-> CHOOSE w \in Value : TRUE]
  /\ majority = 0

\* Transition: scan the next position and update candidate/count. The first
\* position always sets the candidate to its value.
Step ==
  \E i \in Seq :
    /\ scanned' = [scanned EXCEPT ![i] = i]
    /\ IF count = 0 THEN
         /\ candidate' = i
         /\ count' = 1
       ELSE IF candidate = i THEN
         /\ count' = count + 1
         /\ UNCHANGED candidate
       ELSE
         /\ count' = count - 1
         /\ UNCHANGED candidate
    /\ majority' = IF Cardinality(Before(i)) * 2 > 3 THEN i ELSE majority

Spec == Init /\ [][Step]_vars

Inv == TypeOK /\ Correct

====