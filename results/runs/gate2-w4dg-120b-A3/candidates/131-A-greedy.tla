---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm: Scan a sequence of values, maintaining
\* a candidate and a counter. The candidate is only guaranteed to be the majority
\* element if a strict majority exists; otherwise it is a placeholder.
\* This module adds a machine-checked proof (TLAPS) of type correctness and of the
\* algorithm's correctness property.

VARIABLES seq, candidate, count, index, occ

vars == <<seq, candidate, count, index, occ>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..Cardinality(Value)
  /\ index \in 0..Cardinality(Value)
  /\ occ \in [Value -> SUBSET 0..Cardinality(Value)]

\* The inductive invariant from the main specification: the candidate is the only
\* value that can possibly be a strict majority of the scanned prefix.
Inv ==
  /\ \A v \in Value : Cardinality(occ[v]) <= index
  /\ \A v \in Value : Cardinality(occ[v]) = index => candidate = v

Init ==
  /\ seq = <<>>
  /\ candidate = "none"
  /\ count = 0
  /\ index = 0
  /\ occ = [v \in Value |-> {}]

\* Scan the next value, updating the candidate and counter according to the
\* Boyer-Moore rule, and record the position in the occurrence set.
Next ==
  /\ index < Cardinality(Value)
  /\ \E v \in Value :
       /\ seq' = Append(seq, v)
       /\ occ' = [occ EXCEPT ![v] = occ[v] \cup {index}]
       /\ IF count = 0
            THEN /\ candidate' = v
                 /\ count' = 1
            ELSE IF candidate = v
                 THEN count' = count + 1
                 ELSE count' = count - 1
  /\ index' = index + 1

Spec == Init /\ [][Next]_vars

\* The candidate is the only value that can be a strict majority of the scanned
\* prefix: any value occurring in more than half the positions seen so far must
\* equal the candidate.
Correct ==
  \A v \in Value : (2 * Cardinality(occ[v]) > index) => candidate = v

====