---- MODULE MajorityProof ----
EXTENDS MajoritySpec, FiniteSets, Naturals

CONSTANTS Value

VARIABLES seq, pos, cand, count, seen, phase

vars == <<seq, pos, cand, count, seen, phase>>

Init ==
  /\ seq \in [1..3 -> Value]
  /\ pos = 1
  /\ cand = "none"
  /\ count = 0
  /\ seen = {}
  /\ phase = "tally"

Proceed ==
  /\ phase = "tally"
  /\ pos <= Len(seq)
  /\ count' = IF cand = seq[pos] THEN count + 1 ELSE count
  /\ seen' = seen \cup {[idx |-> pos, val |-> seq[pos]]}
  /\ pos' = pos + 1
  /\ cand' = seq[pos]
  /\ phase' = phase
  \/ UNCHANGED <<seq>>

Reset ==
  /\ phase = "tally"
  /\ pos > Len(seq)
  /\ pos' = 1
  /\ cand' = "none"
  /\ count' = 0
  /\ seen' = {}
  /\ phase' = "tally"
  /\ UNCHANGED seq

Reconfigure ==
  /\ phase = "tally"
  /\ \E s \in [1..3 -> Value] : seq' = s
  /\ phase' = "tally"
  /\ pos' = 1
  /\ cand' = "none"
  /\ count' = 0
  /\ seen' = {}
  /\ UNCHANGED <<seq, pos, cand, count, seen, phase>>

Quiesce ==
  /\ phase = "tally"
  /\ phase' = "done"
  /\ UNCHANGED <<seq, pos, cand, count, seen>>

Next == Proceed \/ Reset \/ Reconfigure \/ Quiesce

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ pos \in 0..4
  /\ cand \in (Value \cup {"none"})
  /\ count \in 0..4
  /\ seen \subseteq [idx : 1..3, val : Value]
  /\ phase \in {"tally", "done"}

Inv ==
  /\ (pos > 1) => (Cand \in Value
  /\ count = Cardinality({r \in seen : r.val = cand}))
  /\ (phase = "tally") => (cand = IF pos \in 1..3 THEN seq[pos] ELSE cand)

Correct ==
  (phase = "done") =>
    (\A v \in Value : (2 * Cardinality({r \in seen : r.val = v}) > Cardinality(seen)) => v = Cand)

TypeOKProvable == TypeOK
InvProvable == Inv
CorrectProvable == Correct

====