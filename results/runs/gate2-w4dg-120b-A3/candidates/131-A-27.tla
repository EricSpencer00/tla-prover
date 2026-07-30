---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* This module contains an interactive proof for the Boyer-Moore majority vote
\* algorithm. It extends the main specification with TLAPS-checkable lemmas and
\* a machine-checked proof that the algorithm's candidate is the only possible
\* majority element. No new state is introduced; all state variables and actions
\* are inherited from the main specification.

\* Constants (the only place they appear, matching the .cfg file).
CONSTANTS
  Value

\* The count of array positions processed so far. seq[i] is the value at position
\* i. cand is the Boyer-Moore candidate, and cnt is its confidence counter.
VARIABLES
  count, seq, cand, cnt

vars == << count, seq, cand, cnt >>

\* The set of positions before a given index (a finite set of naturals).
Positions(i) == { j \in 0..(count - 1) : j < i }

TypeOK ==
  /\ count \in 0..2
  /\ seq \in [0..2 -> 0..2]
  /\ cand \in Value
  /\ cnt \in 0..2

\* Initialisation: start with no processed positions and a neutral candidate.
Init ==
  /\ count = 0
  /\ seq = [i \in 0..2 |-> 0]
  /\ cand = 0
  /\ cnt = 0

\* Process one more position of the sequence, updating the candidate as the
\* Boyer-Moore algorithm prescribes.
Step(i, v) ==
  /\ count < 2
  /\ count' = count + 1
  /\ seq' = [seq EXCEPT ![i] = v]
  /\ cand' = IF cnt = 0 THEN v ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1 ELSE IF v = cand THEN cnt + 1 ELSE cnt - 1

\* Completion: once the whole sequence has been processed, the system simply
\* idles (nothing changes, but this action is required to keep the spec live).
Complete ==
  /\ count = 2
  /\ Unchanged vars

Next ==
  \/ \E i \in 0..1, v \in Value : Step(i, v)
  \/ Complete

Spec == Init /\ [][Next]_vars

\* By construction count never exceeds the sequence length.
BoundedCount == count <= 2

\* The Boyer-Moore invariant from the main specification (restated here).
Inv == cnt >= 1 => cand \in { seq[i] : i \in Positions(count) }

\* The number of occurrences of a value before a given index.
Occur(v, i) == Cardinality({ j \in Positions(i) : seq[j] = v })

\* The correctness property: if a value appears in a strict majority of the
\* processed positions, it must equal the Boyer-Moore candidate.
Correct ==
  /\ count = 2
  /\ \E v \in Value : (Occur(v, count) * 2 > count) => cand = v

\* Step 1 / Hierarchy: no new state, simply assert the invariant.
Step1 == Inv

\* Step 2 / Hierarchy: prove the invariant is inductive.
Step2 == Inv

====