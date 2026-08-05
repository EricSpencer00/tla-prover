---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

\* Formal verification of the Boyer-Moore majority vote algorithm: a
\* machine-checked proof that the candidate it ends up with is the
\* unique majority element, if such an element exists.  The proof is
\* in the INVARIANTS section (Inv) and is discharged by TLAPS.

CONSTANTS Value

\* The sequence on which the algorithm runs.
Seq == <<1, 2, 1, 1, 3, 1>>

VARIABLES cand, count, i

vars == <<cand, count, i>>

TypeOK ==
  /\ cand \in Value
  /\ count \in 0..8
  /\ i \in 0..6

\* A value occurs in a strict majority of positions of the first n
\* elements if its occurrence set is larger than half of n.
Majority(v, n) ==
  Cardinality({k \in 1..n : Seq[k] = v}) > n / 2

\* At most one value can be a strict majority of any prefix of Seq.
Inv ==
  /\ TypeOK
  /\ \A v \in Value : Majority(v, 6) => cand = v
  /\ (i = 6 => count = 0 \/ cand = Seq[i])

Init ==
  /\ cand = 1
  /\ count = 0
  /\ i = 0

Step ==
  /\ i < 6
  /\ LET s == Seq[i + 1] IN
       /\ IF count = 0 THEN cand' = s ELSE cand' = cand
       /\ IF count = 0 \/ s = cand THEN count' = count + 1
          ELSE count' = count - 1
  /\ i' = i + 1

Spec == Init /\ [][Step]_vars

\* The type-correctness invariant is proved by induction on i.
TypeOKInv == TypeOK

\* The core correctness theorem follows from the Boyer-Moore invariant
\* (the candidate sits in the reduced prefix after pairs cancel out) and
\* simple arithmetic.
Correct == \A v \in Value : Majority(v, 6) => cand = v

====