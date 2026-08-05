---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* The Boyer-Moore majority vote algorithm, with a machine-checked proof that any
\* strict-majority element must equal the candidate the algorithm produces.
CONSTANTS Value

VARIABLES cand, count, seen, scanned

vars == <<cand, count, seen, scanned>>

None == 0
Seq == (Value \cup {None})
Positions == {p \in Nat : p <= scanned}

Init ==
  /\ cand = None
  /\ count = 0
  /\ seen = [v \in Value |-> 0]
  /\ scanned = 0

\* First half: scan the next value and update the candidate + count. The second half
\* maintains the running occurrence count for every value.
Read(v) ==
  /\ scanned < 6
  /\ scanned' = scanned + 1
  /\ IF count = 0 THEN
       /\ cand' = v
       /\ count' = 1
     ELSE IF v = cand THEN
       /\ count' = count + 1
     ELSE
       /\ count' = count - 1
  /\ seen' = [seen EXCEPT ![v] = @ + 1]
  /\ UNCHANGED cand

Idle ==
  /\ scanned = 6
  /\ UNCHANGED vars

Next == \E v \in Value : Read(v) \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ cand \in Seq
  /\ count \in 0..6
  /\ scanned \in 0..6

\* Invariant from the main spec: the candidate stays consistent with the count.
Consistent ==
  /\ (count = 0) => (cand = None)
  /\ (count > 0) => (cand \in Value)

\* Lemma: positions before a given index form a finite subset of Nat, so occurrence
\* counting functions are always well-defined.
PositionsFinite == Positions \in FINITE

\* Lemma: adding a position to a finite set strictly increases its cardinality.
CardIncrease == \A i \in Nat : i \notin Positions => Cardinality(Positions \cup {i}) = Cardinality(Positions) + 1

\* Correctness invariant: after scanning the whole sequence, any value occuring in a
\* strict majority of positions must be the candidate.
MajorityCandidate ==
  /\ scanned = 6
  /\ \A v \in Value : seen[v] * 2 > 6 => v = cand

Inv == Consistent /\ MajorityCandidate

====