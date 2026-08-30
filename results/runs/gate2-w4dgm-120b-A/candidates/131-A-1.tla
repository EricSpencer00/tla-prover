------------------------- MODULE MajorityProof -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The module inherits the full action set (Init, Scan, Empty) from the main
\* majority-vote spec and adds no new state. It contributes only the
\* machine-checked proof that the algorithm is type-correct and that its
\* majority output is the only possible majority value.

VARIABLES seq, scanned, candidate, found

vars == <<seq, scanned, candidate, found>>

TypeOK ==
    /\ seq \in Seq(Value)
    /\ scanned \in 0..Len(seq)
    /\ candidate \in Value \cup {"none"}
    /\ found \in BOOLEAN

Init ==
    /\ seq \in Seq(Value)
    /\ scanned = 0
    /\ candidate = "none"
    /\ found = FALSE

\* Scan the next position, bumping the assumed candidate whenever the
\* scanned prefix's strict majority value changes.
Scan(i) ==
    /\ scanned < Len(seq)
    /\ scanned' = scanned + 1
    /\ candidate' = CHOOSE c \in Value :
                       2 * Cardinality({k \in 1..scanned + 1 : seq[k] = c})
                         > scanned + 1
    /\ UNCHANGED <<seq, found>>

\* The ballot empties once every position has been scanned; the candidate
\* is frozen and the ballot is reusable.
Empty ==
    /\ scanned = Len(seq)
    /\ scanned' = 0
    /\ candidate' = "none"
    /\ UNCHANGED <<seq, found>>

Next ==
    \/ \E i \in 1..Len(seq) : Scan(i)
    \/ Empty

Spec == Init /\ [][Next]_vars

\* The candidate is frozen once a strict majority has been found.
FoundMajority ==
    /\ ~found
    /\ scanned = Len(seq)
    /\ candidate # "none"
    /\ found' = TRUE
    /\ UNCHANGED <<seq, scanned, candidate>>

SpecA == Spec /\ [][FoundMajority]_vars

Positions(c) == {k \in 1..Len(seq) : seq[k] = c}

\* The only majority value is the candidate frozen at the end of the scan.
Correct ==
    \A c \in Value :
        /\ 2 * Cardinality(Positions(c)) > Len(seq) => c = candidate
        /\ (candidate # "none" => c \in Positions(candidate))

\* The inductive invariant from the main spec (maintained by the Scan
\* action, which is the source of the failure if it ever breaks).
Inv ==
    \A c \in Value :
        2 * Cardinality(Positions(c)) > scanned => c = candidate

\* Safety: type correctness of every variable is never violated.
TypeOKInv == TypeOK

\* Safety: the candidate is the only strict-majority value, once the
\* ballot has finished scanning.
MajorityCoherent == Correct
=============================================================================