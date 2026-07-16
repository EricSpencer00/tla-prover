------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Initialization: start with an empty sequence, index 0, and no candidate. *)
Init ==
    /\ seq = {}
    /\ i   = 0
    /\ cand = Null
    /\ cnt  = 0

(* Step: either extend the sequence by one element (if not yet at the bound) *)
StepAdd ==
    /\ i < bound
    /\ \E v \in Value :
        /\ seq' = seq \cup {[i + 1 |-> v]}
        /\ i'   = i + 1
        /\ UNCHANGED <<cand, cnt>>

(* Step: run one iteration of the Boyer‑Moore majority algorithm on the
   current sequence. *)
StepVote ==
    /\ i = bound
    /\ \E j \in 1 .. bound :
        LET cur == seq[j] IN
        IF cnt = 0 THEN
            /\ cand' = cur
            /\ cnt'  = 1
        ELSE IF cand = cur THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
        ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
        /\ UNCHANGED <<seq, i>>

(* No‑op step to keep the model from deadlocking once voting is finished. *)
StepDone ==
    /\ i = bound
    /\ cnt \le 1
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == \/ StepAdd
        \/ StepVote
        \/ StepDone

(* The system may start in Init and then repeatedly take steps. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================