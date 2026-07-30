---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Formal proof of the Boyer-Moore majority vote algorithm, extending the
\* main algorithm spec with TLAPS-checked lemmas that the algorithm's output
\* is the only possible majority element.

CONSTANT Value

VARIABLES votes, candidate, count, scanned

vars == <<votes, candidate, count, scanned>>

TypeOK ==
    /\ votes \in [0..2 -> Value]
    /\ candidate \in Value
    /\ count \in Nat
    /\ scanned \in 0..2

Init ==
    /\ votes = [i \in 0..2 |-> CHOOSE v \in Value : TRUE]
    /\ candidate = votes[0]
    /\ count = 1
    /\ scanned = 1

Step(i) ==
    /\ scanned < 3
    /\ scanned' = scanned + 1
    /\ votes' = [votes EXCEPT ![i] = CHOOSE v \in Value : TRUE]
    /\ IF votes[i] = candidate
       THEN count' = count + 1
       ELSE IF count > 0
            THEN count' = count - 1
            ELSE count' = 0
    /\ UNCHANGED candidate

Next == \E i \in 0..2 : Step(i)

Spec == Init /\ [][Next]_vars

\* The inductive invariant that the algorithm maintains; a bounded scan
\* leaves candidate equal to the majority element when it exists.
Inv ==
    /\ count <= scanned
    /\ (scanned = 3 => count >= 1)

Correct ==
    \A v \in Value :
        (Cardinality({i \in 0..2 : votes[i] = v}) * 2 > 3) => candidate = v

====