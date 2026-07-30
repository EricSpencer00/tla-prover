---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

ASSUME Value # {}

VARIABLES seq, candidate, count, index, occ
vars == <<seq, candidate, count, index, occ>>

Init ==
  /\ seq \in [1..3 -> Value]
  /\ candidate = CHOOSE c \in Value : TRUE
  /\ count = 0
  /\ index = 1
  /\ occ = {}

IncCount ==
  /\ index <= 3
  /\ candidate' = IF count = 0 THEN seq[index] ELSE candidate
  /\ count' = IF count = 0 THEN 1 ELSE count + 1
  /\ occ' = occ \cup {index}
  /\ index' = index + 1
  /\ UNCHANGED seq

Done ==
  /\ index = 4
  /\ UNCHANGED <<seq, candidate, count, index, occ>>

Next == IncCount \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ candidate \in Value
  /\ count \in 0..3
  /\ index \in 1..4
  /\ occ \subseteq 1..3

Occurrences(v) == Cardinality({i \in 1..3 : seq[i] = v})
Majority(v) == Occurrences(v) > 1

Correct ==
  /\ index = 4
  /\ \A v \in Value : Majority(v) => v = candidate

\* Note: the hierarchical proof below is written for TLAPS, not for the
\* model checker itself; it makes the steps that must be machine-checked
\* explicit.  The model checker only uses the invariant statements.
Inv ==
  /\ TypeOK
  /\ Correct

PROOF
  \* Prove TypeOK is an invariant.
  1. Init => TypeOK
  2. (TypeOK /\ Next) => TypeOK
  3. QED
  \* Prove Correct is an invariant.
  4. Init => Correct
  5. (Correct /\ Next) => Correct
  6. QED
  \* The overall invariant is the conjunction.
  7. Inv == TypeOK /\ Correct
  8. QED

====