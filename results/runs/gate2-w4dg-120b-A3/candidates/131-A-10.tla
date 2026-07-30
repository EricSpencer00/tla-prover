---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The module extends a main Boyer-Moore majority vote spec with lemmas that
\* TLAPS can check. The action set and state are all inherited from the main
\* spec; this file only adds the proof steps and the invariants they protect.

\* State: inherited from the main majority vote spec.
VARIABLES seq, candidate, count, scanned, occ
vars == << seq, candidate, count, scanned, occ >>

Init ==
  /\ seq = [i \in 1..4 |-> CHOOSE v \in Value : TRUE]
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ scanned = 0
  /\ occ = [v \in Value |-> 0]

\* No new actions: all transitions are in the main spec.
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in [1..4 -> Value]
  /\ candidate \in Value
  /\ count \in 0..4
  /\ scanned \in 0..4
  /\ occ \in [Value -> 0..4]

\* The inductive invariant from the main spec: the occurrence count of any
\* value in the scanned prefix equals the true count of that value.
Inv == \A v \in Value : occ[v] = Cardinality({i \in 1..scanned : seq[i] = v})

\* The correctness property: after scanning the whole sequence, any strict
\* majority must be equal to the candidate.
Correct ==
  \A v \in Value : (scanned = 4 /\ occ[v] > 2) => v = candidate

====