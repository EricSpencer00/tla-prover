---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajoritySpec

CONSTANTS Value

ASSUME Value \in FiniteSets.FinSet
ASSUME Value # {}

VARIABLES seq, pos, cand, seen, finished

vars == <<seq, pos, cand, seen, finished>>

TypeOK ==
  /\ seq \in [1..4 -> Value]
  /\ pos \in 1..5
  /\ cand \in Value
  /\ seen \subseteq 1..4
  /\ finished \in BOOLEAN

Init ==
  /\ seq \in [1..4 -> Value]
  /\ pos = 1
  /\ cand \in Value
  /\ seen = {}
  /\ finished = FALSE

Vote(v) ==
  /\ ~finished
  /\ pos <= 4
  /\ seq[pos] = v
  /\ seen' = seen \cup {pos}
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, cand, finished>>

Advance ==
  /\ ~finished
  /\ pos <= 4
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, cand, seen, finished>>

Finish ==
  /\ ~finished
  /\ pos > 4
  /\ finished' = TRUE
  /\ UNCHANGED <<seq, pos, cand, seen>>

Reset ==
  /\ finished
  /\ pos' = 1
  /\ cand' \in Value
  /\ seen' = {}
  /\ finished' = FALSE
  /\ UNCHANGED <<seq>>

Next ==
  \/ \E v \in Value : Vote(v)
  \/ Advance
  \/ Finish
  \/ Reset

Spec == Init /\ [][Next]_vars

OccurrenceCount(w) == Cardinality({ i \in seen : seq[i] = w })
SeenCount == Cardinality(seen)

Inv == SeenCount = pos - 1

MajorityBound ==
  \A w \in Value : occurrenceCount(w) * 2 > pos - 1 ==> w = cand

====