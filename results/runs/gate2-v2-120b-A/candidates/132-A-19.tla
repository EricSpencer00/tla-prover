---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, TLC

(*-------------------------------------------------------------------*)
(*  Constants (to be instantiated by the .cfg)                        *)
(*-------------------------------------------------------------------*)
CONSTANT A, B, C, bound, Seq

(* The set of possible element values *)
Values == {A, B, C}

(*-------------------------------------------------------------------*)
(*  Variables                                                       *)
(*-------------------------------------------------------------------*)
VARIABLES seq, pos, cand, cnt

(*-------------------------------------------------------------------*)
(*  Helper definitions                                              *)
(*-------------------------------------------------------------------*)
(* pos is the index of the next element to be scanned (1..Len+1) *)
(* cnt is the current counter value                                      *)
(* cand is the current candidate element                                   *)

(*-------------------------------------------------------------------*)
(*  Initial predicate                                               *)
(*-------------------------------------------------------------------)
Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

(*-------------------------------------------------------------------*)
(*  Scan step action                                                *)
(*-------------------------------------------------------------------*)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt'  = 1
          ELSE IF cand = x THEN
              /\ cand' = cand
              /\ cnt'  = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt'  = cnt - 1
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos = Len(seq) + 1
       /\ UNCHANGED <<seq, pos, cand, cnt>>   \* stuttering after scan completes

(*-------------------------------------------------------------------*)
(*  Specification                                                   *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

(*-------------------------------------------------------------------*)
(*  Type-correctness invariant                                      *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq
    /\ pos \in 1..(Len(seq) + 1)
    /\ cand \in Values
    /\ cnt \in Nat

(*-------------------------------------------------------------------*)
(*  Correctness invariant (majority correctness after full scan)    *)
(*-------------------------------------------------------------------*)
Correct ==
    /\ pos = Len(seq) + 1
    /\ (\E maj \in Values :
            (Cardinality({ i \in 1..Len(seq) : seq[i] = maj }) > Len(seq) / 2)
            => cand = maj))

(*-------------------------------------------------------------------*)
(*  Inductive invariant (same as Correct but holds throughout)     *)
(*-------------------------------------------------------------------*)
Inv == Correct

=============================================================================