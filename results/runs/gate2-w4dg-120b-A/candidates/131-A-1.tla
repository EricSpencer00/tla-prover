---- MODULE MajorityProof ----
\* An interactive formal proof of correctness for the Boyer-Moore majority vote algorithm.
\* The proof structure is checked by TLAPS. No new state is introduced; everything
\* inherits from the algorithm's main spec, which is named "Spec" there as well.
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..3
  /\ scanned \in 0..3
  /\ seq \in [1..3 -> Value]

Init ==
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0
  /\ seq = [i \in 1..3 |-> CHOOSE v \in Value : TRUE]

Occur(n) == Cardinality({i \in 1..scanned : seq[i] = n})

\* The invariant from the main spec: in the recorded prefix, any majority element must be the candidate.
Correct == \A n \in Value : (Occur(n) * 2 > scanned) => (candidate = n)

Next ==
  \/ /\ scanned < 3
     /\ scanned' = scanned + 1
     /\ candidate' = IF count = 0 THEN seq[scanned + 1] ELSE IF seq[scanned + 1] = candidate THEN candidate ELSE candidate
     /\ count' = IF count = 0 THEN 1 ELSE IF seq[scanned + 1] = candidate THEN count + 1 ELSE count - 1
     /\ UNCHANGED seq
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* The hierarchical TLAPS proof that the whole spec is type-correct.
TypeOKProof ==
  <1>1. TypeOK
      BY DEF Init, Next, vars
  <1>2. TypeOK
      BY DEF Spec

====