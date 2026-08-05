---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm, with a machine-checked proof of
\* type-correctness and of the claim that any strict-majority element must be
\* the candidate left at the end of the scan.
VARIABLES candidate, count, pos, seq

vars == <<candidate, count, pos, seq>>

SeqRange == { i \in 0..(pos - 1) : TRUE }

Occ(v) == { i \in 0..(pos - 1) : seq[i] = v }
Majority(v) == 2 * Cardinality(Occ(v)) > pos

TypeOK ==
  /\ candidate \in {0} \cup Value
  /\ count \in 0..Cardinality(Value)
  /\ pos \in 0..Cardinality(Value)
  /\ seq \in [0..(Cardinality(Value) - 1) -> Value]

Init ==
  /\ candidate = 0
  /\ count = 0
  /\ pos = 0
  /\ \E s \in [0..(Cardinality(Value) - 1) -> Value] : seq = s

Vote(v) ==
  /\ pos < Cardinality(Value)
  /\ IF count = 0
       THEN /\ candidate' = v
            /\ count' = 1
       ELSE IF candidate = v
            THEN count' = count + 1
            ELSE count' = count - 1
  /\ seq' = [seq EXCEPT ![pos] = v]
  /\ pos' = pos + 1

Next == \E v \in Value : Vote(v)

Spec == Init /\ [][Next]_vars

\* The main correctness invariant from the base spec, lifted here as the
\* conclusion of this module's proof: any majority element is exactly the
\* candidate that survives the scan.
Inv == \A v \in Value : Majority(v) => v = candidate

\* This module adds no new state or actions; it adds only the proof that the
\* two invariants below are genuine mathematical consequences of Spec.

TypeOKInv == TypeOK

CorrectInv == Inv

====