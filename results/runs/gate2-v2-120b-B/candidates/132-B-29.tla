---- MODULE MCMajority ----------------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound
ASSUME bound \in Nat \ {0}

Value == { A, B, C }

BoundedSeq(S) == { s \in Seq(S) : Len(s) \leq bound }

VARIABLES seq, i, cand, cnt

(* Initialize the sequence to any bounded sequence over Value, i to 1,
   and cand and cnt to their default start values. *)
Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cand = IF Len(seq) = 0 THEN A ELSE seq[1]   \* any element when empty
    /\ cnt = 0

(* Update step of the majority vote algorithm *)
Step ==
    /\ i \leq Len(seq)
    /\ IF seq[i] = cand
          THEN cnt' = cnt + 1
          ELSE IF cnt = 0
                  THEN /\ cand' = seq[i]
                       /\ cnt' = 1
                  ELSE /\ cand' = cand
                       /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED <<seq>>

(* When the scan is complete, keep the state unchanged *)
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == \/ Step \/ Done

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================