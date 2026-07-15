---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*----------------------------------------------------------------------
  Constants
  ----------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(* The set of possible element values *)
ValueSet == {A, B, C}

(*----------------------------------------------------------------------
  State variables (inherited from the main majority vote spec)
  ----------------------------------------------------------------------*)
VARIABLES seq, i, cand, count

(*----------------------------------------------------------------------
  Bounded sequence operator: returns the set of all sequences (functions
  from 1..n) over ValueSet with length n where 0 \le n \le bound.
  The constant Seq represents exactly this set.
  ----------------------------------------------------------------------*)
Seq == { s \in [1..n -> ValueSet] : n \in 0..bound }

(*----------------------------------------------------------------------
  Helper: type predicate for the state variables
  ----------------------------------------------------------------------*)
VarsTypeOK ==
    /\ seq \in Seq
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in ValueSet
    /\ count \in Nat

(*----------------------------------------------------------------------
  Type correctness invariant (exposed as the required name)
  ----------------------------------------------------------------------*)
TypeOK == VarsTypeOK

(*----------------------------------------------------------------------
  Initial predicate
  ----------------------------------------------------------------------*)
Init ==
    /\ seq \in Seq
    /\ i = 1
    /\ cand \in ValueSet
    /\ count = 0
    /\ TypeOK

(*----------------------------------------------------------------------
  The three cases of the Boyer-Moore scan step
  ----------------------------------------------------------------------*)
AdoptNewCand ==
    /\ i <= Len(seq)
    /\ count = 0
    /\ i' = i + 1
    /\ cand' = seq[i]
    /\ count' = 1

IncCount ==
    /\ i <= Len(seq)
    /\ count > 0
    /\ seq[i] = cand
    /\ i' = i + 1
    /\ cand' = cand
    /\ count' = count + 1

DecCount ==
    /\ i <= Len(seq)
    /\ count > 0
    /\ seq[i] # cand
    /\ i' = i + 1
    /\ cand' = cand
    /\ count' = count - 1

Finish ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, count>>

Next ==
    \/ AdoptNewCand
    \/ IncCount
    \/ DecCount
    \/ Finish

(*----------------------------------------------------------------------
  The specification
  ----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

(*----------------------------------------------------------------------
  Correctness invariant: after the scan completes, any element that is a
  true majority must equal the candidate.
  ----------------------------------------------------------------------*)
Correct ==
    (i > Len(seq)) =>
        \A v \in ValueSet :
            (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2) => v = cand

(*----------------------------------------------------------------------
  Inductive invariant (the one proved in the original spec).  It
  expresses that the candidate equals the majority of the prefix that
  has been scanned, or that no majority exists in that prefix.
  ----------------------------------------------------------------------*)
Inv ==
    LET scanned == i - 1 IN
    \A v \in ValueSet :
        (Cardinality({ j \in 1..scanned : seq[j] = v }) > scanned / 2) => v = cand

(*----------------------------------------------------------------------
  The required global identifiers for the .cfg file
  ----------------------------------------------------------------------*)
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Correct
INVARIANT Inv

====