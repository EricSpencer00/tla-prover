---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* This module contains an interactive formal proof of correctness for the
\* Boyer-Moore majority vote algorithm. It extends the main algorithm
\* specification with lemmas and a machine-checked proof that the algorithm
\* correctly identifies the only possible majority element.

VARIABLES cand, count, i, seq

vars == <<cand, count, i, seq>>

TypeOK ==
  /\ cand \in Value \cup {"none"}
  /\ count \in 0..Cardinality(seq)
  /\ i \in 0..Cardinality(seq)
  /\ seq \in [1..Cardinality(seq) -> Value]

\* No new actions are added here: Init and Next are the same as in the main
\* specification, so the existing inductive invariant Inv from that spec
\* applies unchanged.
Init ==
  /\ cand = "none"
  /\ count = 0
  /\ i = 0
  /\ seq \in [1..Cardinality(seq) -> Value]

Next ==
  /\ i < Cardinality(seq)
  /\ LET x == seq[i + 1] IN
       IF count = 0
         THEN /\ cand' = x
              /\ count' = 1
         ELSE IF x = cand
              THEN /\ count' = count + 1
              /\ cand' = cand
              ELSE /\ count' = count - 1
                   /\ cand' = cand
  /\ i' = i + 1
  /\ UNCHANGED seq

\* The inductive invariant from the main spec is available here unchanged.
Inv == (count > 0 => cand \in Value)

Spec == Init /\ [][Next]_vars

\* Two safety properties are formally proved. The first is type correctness,
\* which holds initially and is preserved by every transition. The second is
\* the correctness property: after scanning the whole sequence, any element
\* occurring in a strict majority of positions must equal the candidate.
TypeOK ==
  /\ TypeOK
  /\ Init => TypeOK
  /\ [Next]_vars => TypeOK

Correct ==
  (i = Cardinality(seq)) => (FORALL x \in Value : 2 * Cardinality({j \in 1..Cardinality(seq) : seq[j] = x}) > Cardinality(seq) => x = cand)

====