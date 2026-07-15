---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

(*----------------------------------------------------------------------
  Constants
----------------------------------------------------------------------*)
CONSTANTS A, B, C, bound, Seq

(*----------------------------------------------------------------------
  Derived constant: the finite set of possible values
----------------------------------------------------------------------*)
Values == {A, B, C}

(*----------------------------------------------------------------------
  State variables
----------------------------------------------------------------------*)
VARIABLES SeqIn, pos, cand, cnt

(*----------------------------------------------------------------------
  Helper definitions
----------------------------------------------------------------------*)
SeqDomain == 1 .. bound

SeqAtLeastOne(p) == p # ""

(*----------------------------------------------------------------------
  Initial state (Init)
----------------------------------------------------------------------*)
Init ==
    /\ SeqIn \in { s \in [SeqDomain -> Values] : Len(s) <= bound }
    /\ Len(SeqIn) =? Len(SeqIn)   \* keep the same variable name for readability
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(*----------------------------------------------------------------------
  Next-state relation (Next)
----------------------------------------------------------------------*)
Next ==
    \/ /\ pos <= Len(SeqIn)          \* there is an element to scan
       /\ LET cur == SeqIn[pos] IN
          IF cnt = 0 THEN
              /\ cand' = cur
              /\ cnt' = 1
          ELSE IF cand = cur THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED SeqIn
    \/ /\ pos > Len(SeqIn)            \* scan finished, stay idle
       /\ UNCHANGED <<SeqIn, pos, cand, cnt>>

(*----------------------------------------------------------------------
  Specification
----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<SeqIn, pos, cand, cnt>>

(*----------------------------------------------------------------------
  Invariant: Type correctness (TypeOK)
----------------------------------------------------------------------*)
TypeOK ==
    /\ SeqIn \in { s \in [SeqDomain -> Values] : Len(s) <= bound }
    /\ pos \in 1 .. (Len(SeqIn) + 1)
    /\ cand \in Values
    /\ cnt \in Nat

(*----------------------------------------------------------------------
  Invariant: Main correctness property (Correct)
      If a value occurs more than half the time in the whole sequence,
      then after the scan finishes it must be equal to the candidate.
----------------------------------------------------------------------*)
Correct ==
    (pos > Len(SeqIn)) => 
        \A v \in Values :
            (Cardinality({ i \in 1..Len(SeqIn) : SeqIn[i] = v }) > Len(SeqIn) / 2) => cand = v

(*----------------------------------------------------------------------
  Invariant: Inductive invariant (Inv)
      Counter is never negative and does not exceed the number of
      processed elements.
----------------------------------------------------------------------*)
Inv ==
    /\ cnt <= Len(SeqIn) - pos + 1
    /\ cnt >= 0

(*----------------------------------------------------------------------
  The required identifiers listed in the .cfg
----------------------------------------------------------------------*)
SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT Correct
INVARIANT Inv

====