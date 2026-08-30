---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANT Value

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

MaxLen == 3

Values == {1, 2}

Init ==
    /\ candidate = 0
    /\ count = 0
    /\ scanned = 0
    /\ seq = [i \in 1..MaxLen |-> 0]

TypeOK ==
    /\ candidate \in {0} \cup Values
    /\ count \in 0..MaxLen
    /\ scanned \in 0..MaxLen
    /\ seq \in [1..MaxLen -> {0} \cup Values]

InitOK == TypeOK

VotesFor(v) == Cardinality({i \in 1..MaxLen : seq[i] = v})

CandidateAppearsOnlyOnce ==
    /\ candidate # 0 => (candidate = seq[1] /\ count = 1)
    /\ (candidate = 0 => count = 0)

MajorityHasCandidate ==
    \A v \in Values : (VotesFor(v) * 2 > scanned) => (v = candidate)

Inv == CandidateAppearsOnlyOnce /\ MajorityHasCandidate

Next ==
    \/ \E v \in Values :
        /\ scanned < MaxLen
        /\ seq' = [seq EXCEPT ![scanned + 1] = v]
        /\ scanned' = scanned + 1
        /\ candidate' = IF count = 0 THEN v
                        ELSE IF v = candidate THEN candidate
                        ELSE candidate
        /\ count' = IF count = 0 THEN 1
                    ELSE IF v = candidate THEN count + 1
                    ELSE count - 1
    \/ scanned = MaxLen /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====