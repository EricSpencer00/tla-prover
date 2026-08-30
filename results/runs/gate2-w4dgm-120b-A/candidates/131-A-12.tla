--------------------------- MODULE MajorityProof ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES pos, votes, cand, occ, count

vars == <<pos, votes, cand, occ, count>>

TypeOK ==
    /\ pos \in 0..2
    /\ votes \in [0..2 -> Value \cup {"none"}]
    /\ cand \in Value
    /\ occ \subseteq 0..2
    /\ count \in 0..2

Init ==
    /\ pos = 0
    /\ votes = [i \in 0..2 |-> "none"]
    /\ cand = CHOOSE v \in Value : TRUE
    /\ occ = {}
    /\ count = 0

CastVote(v) ==
    /\ pos < 2
    /\ votes[pos] = "none"
    /\ votes' = [votes EXCEPT ![pos] = v]
    /\ pos' = pos + 1
    /\ UNCHANGED <<cand, occ, count>>

SetCandidate(v) ==
    /\ cand' = v
    \/ UNCHANGED <<pos, votes, occ, count>>

Tally(p) ==
    /\ votes[p] # "none"
    /\ p \in PosBefore(pos)
    /\ p \notin occ
    /\ occ' = occ \cup {p}
    /\ count' = count + 1
    /\ UNCHANGED <<pos, votes, cand>>

Next ==
    \/ \E v \in Value : CastVote(v)
    \/ \E v \in Value : SetCandidate(v)
    \/ \E p \in 0..2 : Tally(p)

Spec == Init /\ [][Next]_vars

OccAddSingleton ==
    \A s \in SUBSET (0..2) : \A x \in 0..2 :
        (x \notin s) => Cardinality(s \cup {x}) = Cardinality(s) + 1

PosBefore(n) == {i \in 0..2 : i < n}

Inv ==
    /\ TypeOK
    /\ \A p \in occ : votes[p] = cand
    /\ occ \subseteq PosBefore(pos)
    /\ count = Cardinality(occ)

Correct == Inv

=============================================================================