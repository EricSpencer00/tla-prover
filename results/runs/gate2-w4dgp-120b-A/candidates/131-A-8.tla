---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, i, candidate, count, occ

vars == <<seq, i, candidate, count, occ>>

TypeInvariant ==
    /\ seq \subseteq Value
    /\ i \in 0..Cardinality(seq)
    /\ candidate \in Value
    /\ count \in 0..Cardinality(seq)
    /\ occ \subseteq (0..Cardinality(seq) \times Value)

BLOCK ==
    \E c \in seq : candidate' = c

Init ==
    /\ seq = Value
    /\ i = 0
    /\ candidate = CHOOSE c \in Value : TRUE
    /\ count = 0
    /\ occ = {}

Read(v) ==
    /\ i < Cardinality(seq)
    /\ occ' = occ \cup <<i, v>>
    /\ i' = i + 1
    /\ IF count = 0 THEN candidate' = v /\ count' = count + 1
       ELSE IF v = candidate THEN count' = count + 1
       ELSE count' = count - 1
    /\ UNCHANGED seq

Spec == Init /\ [][Read]_vars

Positions(k, v) == {p \in 0..(Cardinality(seq) - 1) : <<p, v>> \in occ}

OccurrenceLemma ==
    \A k \in 0..Cardinality(seq), v \in Value :
        Cardinality(Positions(k, v)) <= k

CorrectnessLemma ==
    \A v \in Value :
        (Cardinality(Positions(Cardinality(seq), v)) * 2 > Cardinality(seq))
            => v = candidate

Correct == OccurrenceLemma /\ CorrectnessLemma

====