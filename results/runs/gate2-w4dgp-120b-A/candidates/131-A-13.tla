---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value # {}

VARIABLES seq, candidate, count, scanned, candidateVotes, seen

vars == << seq, candidate, count, scanned, candidateVotes, seen >>

None == -1

RECURSIVE occ(_)
occ(S) == LET x == CHOOSE y \in S : TRUE IN (IF x \in seq THEN { seq[x] } ELSE {}) \cup occ(S \ { x })

Init ==
    /\ seq \in [0..2 -> Value]
    /\ candidate = None
    /\ count = 0
    /\ scanned = 0
    /\ candidateVotes = 0
    /\ seen = {}

Read ==
    /\ scanned < 3
    /\ LET x == seq[scanned] IN
        /\ IF count = 0 THEN candidate' = x ELSE candidate' = candidate
        /\ IF candidate = x \/ count = 0 THEN count' = count + 1 ELSE count' = count - 1
    /\ scanned' = scanned + 1
    /\ seen' = seen \cup {scanned}
    /\ UNCHANGED << seq, candidateVotes >>

CountVote ==
    /\ scanned = 3
    /\ candidate # None
    /\ candidateVotes' = candidateVotes + (IF candidate \in occ(seen) THEN 1 ELSE 0)
    /\ UNCHANGED << seq, candidate, count, scanned, seen >>

Next == Read \/ CountVote

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ scanned \in 0..3
    /\ count \in 0..3
    /\ seen \subseteq (0..2)

Inv ==
    \A v \in Value : (3 * candidateVotes > scanned) => (v = candidate)

TypeOKInv == Init => [][TypeOK]_vars

CorrectInv == Init => [][Inv]_vars

====