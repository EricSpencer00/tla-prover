---- MODULE MajorityProof ----
EXTENDS Integer, FiniteSets

CONSTANTS Value

None == "none"

VARIABLES cand, count, i, seq
vars == <<cand, count, i, seq>>

TypeOK ==
  /\ cand \in Value \cup {None}
  /\ count \in Nat
  /\ i \in 0..2
  /\ seq \in [1..2 -> Value]

Init ==
  /\ cand = None
  /\ count = 0
  /\ i = 0
  /\ seq \in [1..2 -> Value]

Vote(v) ==
  /\ i < 2
  /\ i' = i + 1
  /\ seq' = [seq EXCEPT ![i + 1] = v]
  /\ IF v = cand
       THEN count' = count + 1
       ELSE IF count = 0
         THEN cand' = v /\ count' = 1
         ELSE count' = count - 1
  /\ UNCHANGED <<cand>>

Next ==
  \E v \in Value : Vote(v)

Spec ==
  /\ Init
  /\ [][Next]_vars

Inv ==
  /\ cand \in Value \cup {None}
  /\ count \in 0..2
  /\ i \in 0..2
  /\ seq \in [1..2 -> Value]

Correct ==
  /\ i = 2
  /\ \E x \in Value :
       (2 * Cardinality({k \in 1..2 : seq[k] = x}) > 2) => x = cand

====