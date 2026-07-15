---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-------------------------------------------------------------------*)
(*  Constants                                                       *)
(*-------------------------------------------------------------------*)
CONSTANT Value       \* The domain of elements that may appear in the input

(*-------------------------------------------------------------------*)
(*  Input sequence                                                  *)
(*-------------------------------------------------------------------*)
VARIABLES seq

(*-------------------------------------------------------------------*)
(*  Imported state from the main majority vote specification        *)
(*-------------------------------------------------------------------*)
VARIABLES i, cand, count   \* i: current index (1..Len(seq)+1)
                           \* cand: current candidate element
                           \* count: current counter

(*-------------------------------------------------------------------*)
(*  Derived set of all possible values                               *)
(*-------------------------------------------------------------------*)
Values == { v \in Value : TRUE }

(*-------------------------------------------------------------------*)
(*  Type correctness predicate (TypeOK)                             *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ count \in Nat

(*-------------------------------------------------------------------*)
(*  Initialization (INIT)                                           *)
(*-------------------------------------------------------------------*)
Init ==
    /\ i = 1
    /\ cand = CHOOSE v \in Values : TRUE   \* arbitrary element of Values
    /\ count = 0
    /\ seq \in Seq(Values)                 \* seq is a finite sequence of Values

(*-------------------------------------------------------------------*)
(*  Transition relation (NEXT)                                      *)
(*-------------------------------------------------------------------*)
Next ==
    \/ /\ i <= Len(seq)
       /\ \/ /\ count = 0
             /\ cand' = seq[i]
             /\ count' = 1
          \/ /\ count > 0 /\ seq[i] = cand
             /\ cand' = cand
             /\ count' = count + 1
          \/ /\ count > 0 /\ seq[i] # cand
             /\ cand' = cand
             /\ count' = count - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i = Len(seq) + 1
       /\ UNCHANGED <<i, cand, count, seq>>

(*-------------------------------------------------------------------*)
(*  Safety invariant (Inv) – the inductive invariant from the main  *)
(*  specification: after processing the prefix seq[1..i-1], any     *)
(*  element that appears more often than any other in that prefix   *)
(*  must be equal to cand.                                           *)
(*-------------------------------------------------------------------*)
Inv ==
    LET prefix == SubSeq(seq, 1, i - 1) IN
    \A v \in Values :
        (Cardinality({ j \in 1..(i-1) : seq[j] = v }) >
         Cardinality({ j \in 1..(i-1) : seq[j] # cand }))
        => v = cand

(*-------------------------------------------------------------------*)
(*  Correctness property (Correct) – after the whole sequence has    *)
(*  been scanned, if some value occurs in a strict majority then    *)
(*  it must be equal to the final candidate.                         *)
(*-------------------------------------------------------------------*)
Correct ==
    i = Len(seq) + 1 =>
        \A v \in Values :
            (Cardinality({ j \in 1..Len(seq) : seq[j] = v }) >
             Cardinality({ j \in 1..Len(seq) : seq[j] # v }))
            => v = cand

(*-------------------------------------------------------------------*)
(*  Specification (Spec)                                            *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<i, cand, count, seq>>

=============================================================================