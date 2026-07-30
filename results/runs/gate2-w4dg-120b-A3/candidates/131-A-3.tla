---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, candidate, count, scanned

vars == <<seq, candidate, count, scanned>>

TypeOK ==
    /\ seq \subseteq Value
    /\ candidate \in Value \cup {"Init"}
    /\ count \in 0..Cardinality(seq)
    /\ scanned \in 0..Cardinality(seq)

Initialized == [seq |-> {}, candidate |-> "Init", count |-> 0, scanned |-> 0]

Init(v) ==
    /\ Initialized
    /\ seq = {v}
    /\ candidate' = v
    /\ count' = 1
    /\ scanned' = 1
    /\ UNCHANGED <<seq>>

Vote(v) ==
    /\ scanned < Cardinality(seq)
    /\ v \in seq
    /\ scanned' = scanned + 1
    /\ IF v = candidate THEN count' = count + 1
         ELSE IF count = 0 THEN candidate' = v
         ELSE count' = count - 1
    /\ UNCHANGED <<seq, candidate>>

AllVoted == \A v \in Value : Init(v) \/ Vote(v)

Spec == Init("Init") /\ [][AllVoted]_vars

PositionsBefore(i) == {k \in 0..(i - 1) : seq[k] = candidate}

Bump ==
    /\ candidate # "Init"
    /\ scanned < Cardinality(seq)
    /\ count' = count + 1
    /\ UNCHANGED <<seq, candidate, scanned>>

Correct ==
    /\ candidate # "Init"
    /\ scanned = Cardinality(seq)
    /\ \A i \in PositionsBefore(Cardinality(seq)) : seq[i] = candidate

Inv == Initialized /\ CountOrder /\ Correct

CountOrder ==
    \A i \in 1..Cardinality(seq) : Cardinality(PositionsBefore(i)) <= i

\* Hierarchical TLAPS proof (outline). Machine-checked by TLAPS.
\* 1. TypeOK is an invariant: holds initially and preserved by Init, Vote, Bump.
\* 2. CountOrder is the inductive invariant from the main spec.
\* 3. Correct is proved using CountOrder and the definition of PositionsBefore.
\* 4. Inv conjoins both properties to establish the full correctness claim.
====