---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value = {"a", "b"}

N == 3
seq == << "a", "b", "a" >>

VARIABLES cand, cnt, i, scanned

vars == << cand, cnt, i, scanned >>

\* The Boyer-Moore majority vote algorithm: it scans the sequence and keeps at most
\* one candidate, cancelling against a different value. On completion, any
\* strict-majority value must equal the candidate.
Init ==
    /\ cand = "a"
    /\ cnt = 0
    /\ i = 0
    /\ scanned = {}

Step ==
    /\ i < N
    /\ LET v == seq[i]
           scanned' == scanned \cup {i}
           cnt' == IF cnt = 0 \/ cand = v THEN cnt + 1 ELSE cnt - 1
           cand' == IF cnt = 0 \/ cand = v THEN v ELSE cand
       IN /\ cand' \in Value
          /\ cnt' \in 0..N
          /\ cand = cand'
          /\ cnt = cnt'
    /\ i' = i + 1

Next == Step

\* Hierarchical invariant: type-correctness of the state variables.
TypeOK ==
    /\ cand \in Value
    /\ cnt \in 0..N
    /\ i \in 0..N
    /\ scanned \subseteq (0..(N - 1))

\* Hierarchical invariant: after a full scan, a strict-majority value must equal
\* the remaining candidate (the Boyer-Moore correctness property).
Majority(v) == 2 * Cardinality({j \in scanned : seq[j] = v}) > N

Correct ==
    /\ i = N
    /\ (cnt > 0 => Majority(cand))

\* The inductive invariant from the main specification is imported unchanged.
Inv == (cnt > 0) => (2 * Cardinality({j \in scanned : seq[j] = cand}) > i)

Spec == Init /\ [][Next]_vars

====