---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* Type correctness: every position's label is a legal value or the
\* placeholder; the candidate is always a legal value or the placeholder.
TypeOK ==
  /\ \A i \in {1, 2, 3} : label[i] \in Value \cup {"none"}
  /\ candidate \in Value \cup {"none"}

\* An occurrence-count predicate: a value occurs in at least one strict-majority position.
Majority(v) ==
  2 * Cardinality({i \in {1, 2, 3} : label[i] = v}) > Cardinality({1, 2, 3})

\* The candidate, once set, always equals the true majority value once it exists.
Correct ==
  \A v \in Value : Majority(v) => candidate = v

\* The BoundedCounter's formal inductive invariant (preserved by every transition).
Inv ==
  /\ \A i \in {1, 2, 3} : label[i] \in Value \cup {"none"}
  /\ candidate \in Value \cup {"none"}
  /\ (\A v \in Value : Majority(v) => candidate = v)

VARIABLES label, candidate

vars == <<label, candidate>>

Init ==
  /\ label = [i \in {1, 2, 3} |-> "none"]
  /\ candidate = "none"

Assign(i, v) ==
  /\ label[i] = "none"
  /\ label' = [label EXCEPT ![i] = v]
  /\ candidate' = IF candidate = "none" THEN v ELSE candidate

Tally(i) ==
  /\ label[i] # "none"
  /\ candidate # "none"
  /\ label' = [label EXCEPT ![i] = candidate]
  /\ UNCHANGED candidate

Next ==
  \/ \E i \in {1, 2, 3}, v \in Value : Assign(i, v)
  \/ \E i \in {1, 2, 3} : Tally(i)

Spec == Init /\ [][Next]_vars

TypeOKSpec == TypeOK
CorrectSpec == Correct

====