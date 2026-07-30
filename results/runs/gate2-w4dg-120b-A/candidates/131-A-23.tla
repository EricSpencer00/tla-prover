---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES seen, cand, cnt, pos, candidate, count

vars == <<seen, cand, cnt, pos, candidate, count>>

TypeOK ==
  /\ seen \subseteq Value
  /\ cand \in Value \cup {"none"}
  /\ cnt \in 0..3
  /\ pos \in 0..3
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..3

Positions == 0..2
Occur(x) == {i \in Positions : seen[i] = x}
Majority(x) == 2 * Cardinality(Occur(x)) > 3

Init ==
  /\ seen = [i \in Positions |-> "none"]
  /\ cand = "none"
  /\ cnt = 0
  /\ pos = 0
  /\ candidate = "none"
  /\ count = 0

Next ==
  /\ \E v \in Value :
       /\ seen' = [seen EXCEPT ![pos] = v]
       /\ cand' = IF cnt = 0 THEN v ELSE cand
       /\ cnt' = IF cnt = 0 THEN 1 ELSE IF cand = v THEN cnt + 1 ELSE cnt - 1
  /\ pos' = IF pos < 3 THEN pos + 1 ELSE pos
  /\ UNCHANGED <<candidate, count>>

Spec == Init /\ [][Next]_vars

Inv == candidate = cand

Correct ==
  /\ \A x \in Value : Majority(x) => x = candidate
  /\ Inv

====