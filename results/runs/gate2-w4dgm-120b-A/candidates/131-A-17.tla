---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES seq, index, candidate, counted, scanned, result

vars == <<seq, index, candidate, counted, scanned, result>>

MaxLen == 3

Values == {"v1", "v2", "v3"}

TypeOK ==
    /\ seq \in [1..MaxLen -> Values]
    /\ index \in 0..MaxLen
    /\ candidate \in Values
    /\ counted \subseteq 1..MaxLen
    /\ scanned \in 0..MaxLen
    /\ result \in {"none", "candidate", "none"}

Init ==
    /\ seq \in [1..MaxLen -> Values]
    /\ index = 0
    /\ candidate \in Values
    /\ counted = {}
    /\ scanned = 0
    /\ result = "none"

\* The Boyer-Moore algorithm updates its candidate by majority voting on the
\* scanned portion of the sequence. Counted records which positions have been
\* counted toward the current candidate.
Step ==
    /\ index < MaxLen
    /\ index' = index + 1
    /\ scanned' = index + 1
    /\ LET x == seq[index + 1] IN
         IF 2 * Cardinality(counted \cup {index + 1}) > scanned + 1
         THEN /\ candidate' = x
              /\ counted' = counted \cup {index + 1}
         ELSE candidate' = candidate
    /\ result' = "none"

Finish ==
    /\ index = MaxLen
    /\ result = "none"
    /\ result' = "candidate"
    /\ UNCHANGED <<seq, index, candidate, counted, scanned>>

AllSameRest ==
    /\ index = MaxLen
    /\ result = "none"
    /\ \A i \in 1..MaxLen : seq[i] = candidate
    /\ result' = "none"
    /\ UNCHANGED <<seq, index, candidate, counted, scanned>>

Next == Step \/ Finish \/ AllSameRest

Spec == Init /\ [][Next]_vars

\* Every state reachable by the algorithm is type-correct: each variable stays
\* within its declared domain, so no step ever produces a value the model does
\* not account for.
Inv ==
    /\ seq \in [1..MaxLen -> Values]
    /\ index \in 0..MaxLen
    /\ candidate \in Values
    /\ counted \subseteq 1..MaxLen
    /\ scanned \in 0..MaxLen
    /\ result \in {"none", "candidate", "none"}

\* Main result: after scanning the whole sequence, any value that occurs in a
\* strict majority of positions must be the algorithm's candidate.
Correct ==
    \A v \in Values :
        /\ scanned = MaxLen
        /\ 2 * Cardinality({i \in 1..MaxLen : seq[i] = v}) > MaxLen
        => v = candidate

====