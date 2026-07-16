---- MODULE MCMajority ----------------------------------------------
EXTENDS Integers

\* The constant `bound` must be a natural number (including zero).  The
\* original specification incorrectly asserted `bound \notin Nat`,
\* which makes the module inconsistent and prevents TLC from starting.
\* We replace it with the correct assumption that `bound` belongs to the
\* set of natural numbers.
ASSUME bound \in Nat

CONSTANTS A, B, C
VARIABLES seq, i, cand, cnt

\* The set of possible vote values.
Value == {A, B, C}

\* All sequences over `Value` whose length does not exceed `bound`.
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ seq = {}
    /\ i   = 0
    /\ cand = CHOOSE v \in Value : TRUE   \* any value, won't be used until i>0
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* The classic Boyer‑Moore majority‑vote step.
Step ==
    /\ i < bound
    /\ i' = i + 1
    /\ \E v \in Value :
          /\ seq' = [seq EXCEPT ![i'] = v]
          /\ IF cnt = 0
                THEN /\ cand' = v
                     /\ cnt'  = 1
                ELSE IF v = cand
                        THEN /\ cand' = cand
                             /\ cnt'  = cnt + 1
                        ELSE /\ cand' = cand
                             /\ cnt'  = cnt - 1

\* ----------------------------------------------------------------------
\* After `i = bound` the algorithm may optionally verify the candidate.
Final ==
    /\ i = bound
    /\ cand \in Value

\* ----------------------------------------------------------------------
\* The overall behavior of the system.
Next == Step \/ Final

\* ----------------------------------------------------------------------
\* Safety invariant: the candidate is always a member of the allowed
\* values whenever the algorithm has processed at least one element.
CandInValue ==
    /\ i > 0
    /\ cand \in Value

\* ----------------------------------------------------------------------
\* The specification (no environment actions, just the algorithm).
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================