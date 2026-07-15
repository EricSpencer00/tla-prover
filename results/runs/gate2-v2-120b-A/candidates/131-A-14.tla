---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Values == {v \in Value : TRUE}
Idxs   == Nat

(*--------------------------------------------------------------------
  State variables (inherited from the main majority vote spec)
--------------------------------------------------------------------*)
VARIABLES seq, idx, cand, cnt

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Seq == seq
Idx == idx
Cand == cand
Cnt == cnt

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
    /\ seq \in [Idx -> Values]            \* a finite sequence indexed by Nat
    /\ idx = 1
    /\ cand \in Values
    /\ cnt = 0

(*--------------------------------------------------------------------
  Transition relation (Boyer-Moore majority vote step)
--------------------------------------------------------------------*)
Next ==
    /\ idx <= Len(seq) + 1
    /\ IF idx <= Len(seq) THEN
          IF cnt = 0 THEN
              /\ cand' = seq[idx]
              /\ cnt'  = 1
          ELSE IF seq[idx] = cand THEN
              /\ cnt' = cnt + 1
          ELSE
              /\ cnt' = cnt - 1
       ELSE
          /\ UNCHANGED <<seq, cand, cnt>>
    /\ idx' = idx + 1

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, idx, cand, cnt>>

(*--------------------------------------------------------------------
  Invariant: type correctness
--------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in [Idx -> Values]
    /\ idx \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

(*--------------------------------------------------------------------
  Invariant: main correctness property (the candidate after the scan
  is the only possible majority element)
--------------------------------------------------------------------*)
Correct ==
    /\ idx = Len(seq) + 1
    /\ (\A v \in Values :
          Cardinality({ i \in 1..Len(seq) : seq[i] = v }) >
          Len(seq) / 2 => v = cand)

(*--------------------------------------------------------------------
  Auxiliary invariant (copied from the original algorithm spec)
--------------------------------------------------------------------*)
Inv ==
    /\ idx \in 1..(Len(seq) + 1)
    /\ (cnt = 0 => cand \in Values)

(*--------------------------------------------------------------------
  THEOREM: All invariants hold under Spec
--------------------------------------------------------------------*)
THEOREM SpecImpliesTypeOK == Spec => []TypeOK
THEOREM SpecImpliesCorrect == Spec => []Correct
THEOREM SpecImpliesInv == Spec => []Inv

=============================================================================