---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES candidate, count, pos, v

vars == <<candidate, count, pos, v>>

Majority == CHOOSE w \in Value : TRUE

TypeOK ==
    /\ candidate \in Value
    /\ count \in 0..3
    /\ pos \in 0..3
    /\ v \in [0..3 -> Value]

Inv ==
    /\ candidate \in Value
    /\ count \in 0..3
    /\ pos \in 0..3
    /\ v \in [0..3 -> Value]

Init ==
    /\ candidate = Majority
    /\ count = 0
    /\ pos = 0
    /\ v = [i \in 0..3 |-> Majority]

Step ==
    /\ pos < 3
    /\ LET x == IF candidate = v[pos] THEN count + 1 ELSE 0 IN
         /\ candidate' = IF x = 0 THEN v[pos] ELSE candidate
         /\ count' = x
    /\ pos' = pos + 1
    /\ v' = [v EXCEPT ![pos] = v[pos]]

Spec == Init /\ [][Step]_vars

\* Majority element correctness: after scanning the whole sequence, any value
\* occuring in more than half the positions must equal the candidate.
Correct ==
    /\ pos = 3
    /\ \A w \in Value :
         (2 * Cardinality({i \in 0..(pos - 1) : v[i] = w}) > pos) => (w = candidate)

====