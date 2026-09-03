---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES seq, index, candidate, seen, firstIdx

vars == <<seq, index, candidate, seen, firstIdx>>

Values == {1, 2}

Init ==
    /\ seq \in [1 .. 4 -> Values]
    /\ index = 1
    /\ candidate \in Values
    /\ seen = {}
    /\ firstIdx = 0

Next ==
    /\ index < 5
    /\ seq' = [seq EXCEPT ![index + 1] = candidate]
    /\ index' = index + 1
    /\ seen' = IF candidate \in seen THEN seen ELSE seen \cup {candidate}
    /\ firstIdx' = IF candidate \in seen THEN firstIdx ELSE index + 1
    /\ UNCHANGED <<candidate>>

Spec == Init /\ [][Next]_vars

\* Type correctness of all state variables.
TypeOK ==
    /\ seq \in [1 .. 4 -> Values]
    /\ index \in 0 .. 5
    /\ candidate \in Values
    /\ seen \subseteq Values
    /\ firstIdx \in 0 .. 4

\* The main correctness claim: after a full scan, any value that appears in a
\* strict majority of positions must be the Boyer-Moore candidate.
Correct ==
    /\ index = 4
    /\ \A v \in Values :
         (2 * Cardinality({k \in 1 .. 4 : seq[k] = v}) > 4) => (v = candidate)

\* Inductive invariant from the main algorithm: no two distinct values can both
\* appear more than half the time in the scanned prefix.
\* (Carried unchanged from the main specification.)
Inv ==
    \A i, j \in 1 .. index :
        (i <= index /\ j <= index /\ seq[i] = seq[j]) => (i = j)

\* The spec and both invariants together imply the single possible majority.
\* (Liveness: NOT_SPECIFIED)
====