---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES scanned, candidate, majorities, seq

vars == <<scanned, candidate, majorities, seq>>

Positions == 0 .. Len(seq) - 1

PositionsBefore(i) == { j \in Positions : j < i }

Occur(v, i) == { j \in PositionsBefore(i) : seq[j] = v }

\* No new state: candidate and majorities are carried over from Spec.
InitSpec ==
    /\ scanned = 0
    /\ candidate = "none"
    /\ majorities = {}
    /\ seq \in (Value \cup {"none"})^1

CONSTANTS
    InitSpec
    Scan
    Reset

NextSpec ==
    \/ Scan
    \/ Reset

Spec == InitSpec /\ [][NextSpec]_vars

CardinalityDefined ==
    \A X \in SUBSET Positions : Cardinality(X) \in Nat

TypeOK ==
    /\ scanned \in 0 .. Len(seq)
    /\ candidate \in Value \cup {"none"}
    /\ majorities \subseteq Value
    /\ CardinalityDefined

Inv ==
    /\ candidate = "none"
    /\ majorities = {}
    /\ scanned \in {0, Len(seq)}

\* Scan: compare the new element's occurrences against the current candidate.
Scan ==
    /\ scanned < Len(seq)
    /\ candidate' = IF candidate = "none" THEN seq[scanned]
                    ELSE IF 2 * Cardinality(Occur(seq[scanned], scanned + 1))
                              > scanned + 1
                          THEN seq[scanned] ELSE candidate
    /\ majorities' = IF 2 * Cardinality(Occur(seq[scanned], scanned + 1))
                         > scanned + 1
                     THEN {seq[scanned]} ELSE majorities
    /\ scanned' = scanned + 1
    /\ UNCHANGED seq

\* Reset: scan a fresh sequence, keeping no stale candidate or majority.
Reset ==
    /\ scanned = Len(seq)
    /\ seq' \in (Value \cup {"none"})^1
    /\ scanned' = 0
    /\ candidate' = "none"
    /\ majorities' = {}
    /\ UNCHANGED seq

TypeOKIsInvariant == TypeOK /\ [][TypeOK]_vars
CorrectnessIsInvariant == Inv /\ [][Inv]_vars

====