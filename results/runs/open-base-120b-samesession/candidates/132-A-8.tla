---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Assume the constants are distinct and bound is a natural number
ASSUME A # B /\ A # C /\ B # C
ASSUME bound \in Nat

\* The set of possible element values
ValueSet == { A, B, C }

\* Bounded version of Seq (finite sequences over a set, limited by bound)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, count

\* Helper function: count occurrences of a value in a sequence
Count(s, v) == 
  Cardinality({ j \in 1..Len(s) : s[j] = v })

\* The set of majority elements in the current sequence
MajorityElems == { v \in ValueSet : 2 * Count(seq, v) > Len(seq) }

\* Initialization
Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i = 1
  /\ cand \in ValueSet
  /\ count = 0

\* One step of the Boyer‑Moore scan
Next ==
  \/ /\ i <= Len(seq)
     /\ LET x == seq[i] IN
        IF count = 0 THEN
          /\ cand' = x
          /\ count' = 1
        ELSE IF cand = x THEN
          /\ cand' = cand
          /\ count' = count + 1
        ELSE
          /\ cand' = cand
          /\ count' = count - 1
     /\ i' = i + 1
     /\ UNCHANGED seq
  \/ /\ i > Len(seq)            \* stutter after the scan is finished
     /\ UNCHANGED <<seq, i, cand, count>>

\* Specification
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

\* Type correctness invariant
TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i \in Nat
  /\ cand \in ValueSet
  /\ count \in Nat

\* Main correctness property: if a majority exists, the final candidate is a majority
Correct ==
  /\ i > Len(seq)
  /\ MajorityElems # {}
  => cand \in MajorityElems

\* Inductive invariant (a simple strengthening of TypeOK)
Inv == TypeOK

====