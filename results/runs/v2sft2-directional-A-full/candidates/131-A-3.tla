---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT Value

\* ----------------------------------------------------------------------
\* State variables inherited from the main majority vote specification
\* ----------------------------------------------------------------------
VARIABLES data, i, cand, cnt

\* ----------------------------------------------------------------------
\* Helper predicates and definitions
\* ----------------------------------------------------------------------
PositionsBefore(n) == {j \in 0 .. n-1}

OccurrencesBefore(n, v) ==
    {j \in 0 .. n-1 : data[j] = v}

\* ----------------------------------------------------------------------
\* Type correctness invariant (TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ data \in Seq(Value)
    /\ i \in Nat
    /\ cand \in Value
    /\ cnt \in Nat
    /\ Len(data) = i

\* ----------------------------------------------------------------------
\* Correctness invariant (Correct)
\* ----------------------------------------------------------------------
Correct ==
    \A v \in Value :
        (Count(data, v) > Len(data) / 2) => (v = cand)

\* ----------------------------------------------------------------------
\* Combined invariant (Inv) used in SPECIFICATION
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Correct

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ data = << >>
    /\ i = 0
    /\ cand \in Value
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Incremental update of the majority vote algorithm (NEXT)
\* ----------------------------------------------------------------------
Next ==
    /\ i < Len(data)
    /\ LET elt == data[i] IN
        IF cnt = 0 THEN
            /\ cand' = elt
            /\ cnt' = 1
            /\ i' = i + 1
        ELSE
            IF cand = elt THEN
                /\ cnt' = cnt + 1
                /\ i' = i + 1
                /\ cand' = cand
            ELSE
                /\ cnt' = cnt - 1
                /\ i' = i + 1
                /\ cand' = cand

\* ----------------------------------------------------------------------
\* Specification of the system
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<data, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* Safety properties (invariants)
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Correct
INVARIANT Inv

====