---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

VARIABLES seq, pos, cand, count, scanned

vars == <<seq, pos, cand, count, scanned>>

TypeOK ==
    /\ seq \in Seq(Value)
    /\ pos \in 0..Len(seq)
    /\ cand \in Value \cup {"none"}
    /\ count \in 0..Len(seq)
    /\ scanned \in BOOLEAN

Init ==
    /\ seq = << >>
    /\ pos = 0
    /\ cand = "none"
    /\ count = 0
    /\ scanned = FALSE

Append(v) ==
    /\ seq' = Append(seq, v)
    /\ UNCHANGED <<pos, cand, count, scanned>>

SetCandidate(v) ==
    /\ cand = "none"
    /\ cand' = v
    /\ count' = 1
    /\ UNCHANGED <<seq, pos, scanned>>

MatchCandidate(v) ==
    /\ cand # "none"
    /\ v = cand
    /\ count' = count + 1
    /\ UNCHANGED <<seq, pos, cand, scanned>>

Mismatch(v) ==
    /\ cand # "none"
    /\ v # cand
    /\ UNCHANGED <<seq, pos, cand, count, scanned>>

Scan ==
    /\ pos < Len(seq)
    /\ pos' = pos + 1
    /\ scanned' = (pos + 1 = Len(seq))
    /\ UNCHANGED <<seq, cand, count>>

Next ==
    \/ \E v \in Value : Append(v)
    \/ \E v \in Value : SetCandidate(v)
    \/ \E v \in Value : MatchCandidate(v)
    \/ \E v \in Value : Mismatch(v)
    \/ Scan

Spec == Init /\ [][Next]_vars

Inv ==
    /\ TypeOK
    /\ \A i \in 1..Len(seq) : seq[i] \in Value
    /\ (cand # "none") => (count = Cardinality({i \in 1..Len(seq) : seq[i] = cand}))
    /\ scanned => (pos = Len(seq))

Correct ==
    \A v \in Value :
        (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)) => (v = cand)

====