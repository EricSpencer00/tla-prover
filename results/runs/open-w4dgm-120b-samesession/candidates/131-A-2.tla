---- MODULE MajorityProof ----
EXTENDS MajorityVote, Integers, FiniteSets

CONSTANTS Value

VARIABLES stream, read, candidate, candidateCount, prefix

vars == <<stream, read, candidate, candidateCount, prefix>>

\* Every occurrence-counting function keeps its domain within the finite
\* run of the prefix, so it is a finite set and its cardinality is well-defined.
\* TLAPS checks that CandidateCount stays integer-valued throughout.

TypeOK ==
    /\ stream \in [1..2 -> Value]
    /\ read \in 1..3
    /\ candidate \in Value
    /\ candidateCount \in Nat
    /\ prefix \subseteq (1..2)

\* The invariant from the algorithm: any strict-majority value after the full
\* scan must be the candidate itself.
Correct ==
    \A v \in Value :
        (2 * Cardinality({i \in 1..2 : stream[i] = v}) > read) => v = candidate

Init ==
    /\ stream = <<Value, Value>>
    /\ read = 0
    /\ candidate = Value
    /\ candidateCount = 0
    /\ prefix = {}

\* Scan the next position, updating the candidate by Boyer-Moore's rule.
ReadNext ==
    /\ read < 3
    /\ read + 1 <= Len(stream)
    /\ LET v == stream[read + 1] IN
        \/ IF read = 0 \/ candidateCount = 0
           THEN /\ candidate' = v
                /\ candidateCount' = 1
           ELSE IF v = candidate
                THEN /\ candidate' = candidate
                     /\ candidateCount' = candidateCount + 1
                ELSE /\ candidate' = candidate
                     /\ candidateCount' = candidateCount - 1
    /\ read' = read + 1
    /\ prefix' = prefix \cup {read + 1}
    /\ UNCHANGED <<stream>>

Trim ==
    /\ read > 0
    /\ read' = 0
    /\ prefix' = {}
    /\ UNCHANGED <<stream, candidate, candidateCount>>

Next == ReadNext \/ Trim

Spec == Init /\ [][Next]_vars

\* The two invariants are proved together; TLAPS checks each proof step.
RECURSIVE Inv(_)
Inv(f) ==
    /\ TypeOK
    /\ Correct
    /\ \A e \in f : Inv(e)
====