---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets
CONSTANTS Value

None == "none"
MaxN == 3

VARIABLES candidate, count, i, seq, candidatePos

TypeOK ==
    /\ candidate \in (Value \cup {None})
    /\ count \in 0..MaxN
    /\ i \in 0..MaxN
    /\ seq \in [1..MaxN -> Value]
    /\ candidatePos \in SUBSET (1..MaxN)

Init ==
    /\ candidate = None
    /\ count = 0
    /\ i = 0
    /\ seq \in [1..MaxN -> Value]
    /\ candidatePos = {}

Bump(c) == IF c < MaxN THEN c + 1 ELSE c

Next ==
    /\ i < MaxN
    /\ count' = Bump(count)
    /\ i' = Bump(i)
    /\ candidate' = seq[i + 1]
    /\ candidatePos' = candidatePos \cup {i + 1}
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_<<candidate, count, i, seq, candidatePos>>

\* Lemma: the positions before a given index form a finite set of the right size.
PositionsBefore(i) == { x \in 1..i : TRUE }

Inv ==
    /\ candidate \in (Value \cup {None})
    /\ count \in 0..MaxN
    /\ i \in 0..MaxN
    /\ candidatePos \subseteq (1..MaxN)
    /\ 2 * Cardinality(candidatePos) >= i

\* Lemma: any strict majority value must be the candidate.
Correct ==
    \A v \in Value :
        (Cardinality({x \in 1..MaxN : seq[x] = v}) * 2 > MaxN)
            => v = candidate

====