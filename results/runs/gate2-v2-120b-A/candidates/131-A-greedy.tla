---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Value

(*--------------------------------------------------------------------
  State variables (inherited from the main majority vote specification)
--------------------------------------------------------------------*)
VARIABLES seq, i, cand, cnt

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
SeqLen == Len(seq)

(* The set of all possible values *)
Values == Value

(*--------------------------------------------------------------------
  Type correctness invariant (TypeOK)
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Values)
  /\ i \in 0..SeqLen
  /\ cand \in Values
  /\ cnt \in Nat

(*--------------------------------------------------------------------
  Initial state (inherited from the main specification)
--------------------------------------------------------------------*)
Init ==
  /\ seq = <<>>               \* placeholder: the actual sequence is supplied by the model
  /\ i = 0
  /\ cand \in Values
  /\ cnt = 0

(*--------------------------------------------------------------------
  Transition relation (inherited from the main specification)
--------------------------------------------------------------------*)
Next ==
  \/ /\ i < SeqLen
     /\ LET cur == seq[i+1] IN
        IF cnt = 0 THEN
          /\ cand' = cur
          /\ cnt' = 1
        ELSE IF cand = cur THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
        ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
     /\ i' = i + 1
     /\ UNCHANGED <<seq>>
  \/ /\ i = SeqLen
     /\ UNCHANGED <<seq, i, cand, cnt>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*--------------------------------------------------------------------
  Main correctness invariant (Correct)
--------------------------------------------------------------------*)
Correct ==
  /\ i = SeqLen
  /\ \A v \in Values :
        (Cardinality({ j \in 1..SeqLen : seq[j] = v }) > SeqLen / 2) => v = cand

(*--------------------------------------------------------------------
  Additional invariant (Inv) – the inductive invariant from the main spec
--------------------------------------------------------------------*)
Inv ==
  /\ i \in 0..SeqLen
  /\ cnt >= 0
  /\ (cnt = 0 => cand \in Values)
  /\ (cnt > 0 => cand = seq[i]) \* simplified version for illustration

(*--------------------------------------------------------------------
  Theorems (optional, for TLAPS)
--------------------------------------------------------------------*)
THEOREM TypeOKIsInvariant == Spec => []TypeOK
THEOREM CorrectIsInvariant == Spec => []Correct
THEOREM InvIsInvariant == Spec => []Inv

====