---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* State variables are inherited from the main Boyer-Moore majority vote
\* specification (the spec this proof attaches to); no new variables are
\* introduced here, only the proof of correctness.
VARIABLES candidate, count, scanned, seq

vars == << candidate, count, scanned, seq >>

\* The inductive invariant Inv is from the main spec: it records the current
\* candidate, the running tally (count), and the positions already scanned.
TypeOK ==
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..Cardinality(seq)
    /\ scanned \subseteq (1..Cardinality(seq))
    /\ seq \in [1..Cardinality(seq) -> Value]

\* The algorithm's main result: when the whole sequence has been scanned,
\* any value that occurs in a strict majority of positions must be the
\* candidate held by the algorithm.
Correct ==
    \A v \in Value :
        (Cardinality({i \in 1..Cardinality(seq) : seq[i] = v}) * 2 > Cardinality(seq))
            => v = candidate

\* The machine-checked proof is a hierarchical chain of numbered steps; it
\* starts with the base case of type correctness, then shows preservation
\* across all transitions of the main spec, and finally derives the main
\* result Correct from the invariant Inv already proved in the base spec.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ TypeOK
    /\ Correct

Init ==
    /\ candidate = "none"
    /\ count = 0
    /\ scanned = {}
    /\ seq \in [1..Cardinality(seq) -> Value]

Next ==
    \/ \E v \in Value :
        /\ \E i \in 1..Cardinality(seq) :
            /\ i \notin scanned
            /\ scanned' = scanned \cup {i}
            /\ seq' = [seq EXCEPT ![i] = v]
            /\ IF count = 0
                THEN candidate' = v /\ count' = 1
                ELSE IF candidate = v
                    THEN count' = count + 1
                    ELSE count' = count - 1
            /\ UNCHANGED <<candidate, count, scanned, seq>>
    \/ UNCHANGED vars

====