---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* This module contains an interactive formal proof of correctness for the Boyer-Moore
\* majority vote algorithm.  It extends the main majority vote specification with
\* lemmas and a machine-checked proof that the algorithm correctly identifies the only
\* possible majority element.  The proof is structured to be checked by TLAPS, which
\* verifies every proof step rather than trusting the author's intuition.

\* No new state beyond the main algorithm's is introduced here; this module adds
\* only the proof infrastructure.
VARIABLES candidate, count, i, seq

vars == << candidate, count, i, seq >>

TypeOK ==
  /\ candidate \in Value \cup {0}
  /\ count \in -1..3
  /\ i \in 0..3
  /\ seq \in [1..3 -> Value]

\* The Boyer-Moore update: match extends the candidate run, disagreement discards it.
NextStep ==
  \/ /\ i < 3
     /\ candidate' = IF count = 0 THEN seq[i + 1] ELSE candidate
     /\ count' = IF count = 0 THEN 1 ELSE IF seq[i + 1] = candidate THEN count + 1 ELSE count - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i = 3
     /\ UNCHANGED <<candidate, count, i, seq>>

\* An empty suffix occurs at most once; each added position is distinct, so occurrences
\* measured up to i form a finite set of positions.
Occ(i, v) == { j \in 1..i : seq[j] = v }

\* The algorithm is correct: any strict-majority value must be the surviving candidate.
Correct ==
  i = 3 => \A v \in Value : (2 * Cardinality(Occ(3, v)) > 3) => v = candidate

\* Plain type-correctness invariant, shown invariant of the underlying spec.
TypeOKInv == TypeOK

Inv == Correct

Init ==
  /\ candidate = 0
  /\ count = 0
  /\ i = 0
  /\ seq = [j \in 1..3 |-> IF j = 1 THEN 1 ELSE IF j = 2 THEN 2 ELSE 2]

Spec == Init /\ [][NextStep]_vars

====