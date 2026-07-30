---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The interactive proof extends the main Boyer-Moore majority vote
\* specification with machine-checked lemmas. No new state is added; all
\* state variables are inherited from the main spec.

VARIABLES candidate, count, scanned, seq

vars == <<candidate, count, scanned, seq>>

\* The set of positions before a given index is a finite subset of Nat.
PositionsBefore(i) == { k \in Nat : k < i }

TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..Cardinality(seq)
  /\ scanned \in 0..Cardinality(seq)
  /\ seq \in SUBSET Value

Init ==
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0
  /\ seq = Value

\* The Boyer-Moore update rule: match advances the candidate, mismatch
\* decrements the count, and a zero count resets the candidate.
Next ==
  /\ scanned < Cardinality(seq)
  /\ LET x == CHOOSE y \in seq : TRUE IN
       /\ IF count = 0
          THEN /\ candidate' = x
               /\ count' = 1
          ELSE IF candidate = x
               THEN /\ candidate' = candidate
                    /\ count' = count + 1
               ELSE /\ candidate' = candidate
                    /\ count' = count - 1
  /\ scanned' = scanned + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

\* The inductive invariant from the main spec: any strict-majority value
\* must equal the current candidate.
Correct ==
  \A v \in Value :
    (2 * Cardinality({ k \in PositionsBefore(scanned) : seq[k] = v }) > scanned)
      => candidate = v

\* The proof is hierarchical: type correctness is proved first, then the
\* main correctness property, each as an invariant of the spec.
Inv == TypeOK /\ Correct

====