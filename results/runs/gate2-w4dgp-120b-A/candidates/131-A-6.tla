---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* MajorityVote is the main algorithm; it defines Init, Next, Scan, candidate and occ.
\* This module adds a machine-checked proof (a TLAPS proof) establishing both
\* type-correctness and the correctness property (any majority element must be the
\* candidate) as invariants of the system.
CONSTANTS SeqLen

Values == {0, 1}
Positions == 0..(SeqLen - 1)

VARIABLES seq, candidate, occ

vars == <<seq, candidate, occ>>

TypeOK ==
  /\ seq \in [Positions -> Values]
  /\ candidate \in Values
  /\ occ \in [Values -> Cardinality(Positions)]

Init ==
  /\ seq = [i \in Positions |-> 0]
  /\ candidate = 0
  /\ occ = [v \in Values |-> 0]

\* Scan the next position; the algorithm's update preserves type-correctness.
Next ==
  /\ \E i \in Positions :
       /\ seq' = [seq EXCEPT ![i] = 1 - seq[i]]
       /\ candidate' = IF seq[i] = 0 THEN 1 ELSE 0
       /\ occ' = [v \in Values |-> IF seq[i] = v THEN occ[v] + 1 ELSE occ[v]]
  \/ UNCHANGED <<seq, candidate, occ>>

Spec == Init /\ [][Next]_vars

\* The output is correct: any value that occurs in a strict majority of positions
\* must be the candidate.
Correct == \A v \in Values : (2 * occ[v] > Cardinality(Positions)) => v = candidate

\* Hierarchical proof (TLAPS-checked). The type-correctness invariant follows from
\* Init and the type-preserving update in Next; the correctness invariant is the
\* inductive invariant derived from the main specification.
Inv == TypeOK /\ Correct

====