---- MODULE MajorityProof ----
EXTENDS MainSpec, FiniteSets

CONSTANTS Value

VARIABLES seq, idx, cand, seen, phase

vars == <<seq, idx, cand, seen, phase>>

RECURSIVE Occurs(_)
Occurs(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN (IF seq[x] = cand THEN 1 ELSE 0) + Occurs(S \ {x})

TypeOK ==
    /\ seq \in [0..3 -> Value]
    /\ idx \in 0..4
    /\ cand \in Value
    /\ seen \in SUBSET 0..3
    /\ phase \in {"scanning", "done"}

Init ==
    /\ seq \in [0..3 -> Value]
    /\ idx = 0
    /\ cand \in Value
    /\ seen = {}
    /\ phase = "scanning"

Scan ==
    /\ phase = "scanning"
    /\ idx < 4
    /\ cand' = seq[idx]
    /\ seen' = seen \cup {idx}
    /\ idx' = idx + 1
    /\ UNCHANGED <<seq, phase>>

Finish ==
    /\ phase = "scanning"
    /\ idx = 4
    /\ phase' = "done"
    /\ UNCHANGED <<seq, idx, cand, seen>>

Restart ==
    /\ phase = "done"
    /\ phase' = "scanning"
    /\ idx' = 0
    /\ seen' = {}
    /\ UNCHANGED <<seq, cand>>

Next == Scan \/ Finish \/ Restart

Spec == Init /\ [][Next]_vars

Inv == \A v \in Value : (Occurs(0..3) > 2) => (v = cand)

Correct == (phase = "done") => Inv

====