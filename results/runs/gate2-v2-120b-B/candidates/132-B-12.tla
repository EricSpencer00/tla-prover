------------------------- MODULE MCMajority -------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all      *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

(* The bound must be a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Sequences of elements from S with length between 0 and bound. *)
BoundedSeq(S) == { s \in [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Initialization: start with the empty sequence and the default state of the *)
(* Majority algorithm (no candidate, zero count).                           *)
Init ==
    /\ seq = {}
    /\ i   = 0
    /\ cand = {}
    /\ cnt  = 0

(* One step of the Majority algorithm on the next element of the sequence. *)
Next ==
    /\ i < bound
    /\ \E e \in Value :
        /\ seq' = seq \cup [i + 1 |-> e]
        /\ i'   = i + 1
        /\ IF cnt = 0
              THEN /\ cand' = {e}
                   /\ cnt'  = 1
              ELSE IF e \in cand
                      THEN /\ cand' = cand
                           /\ cnt'  = cnt + 1
                      ELSE /\ cand' = cand
                           /\ cnt'  = cnt - 1

(* No further actions once the bound is reached. *)
Done ==
    /\ i = bound
    /\ UNCHANGED << seq, i, cand, cnt >>

(* Behaviour of the system. *)
Spec ==
    Init /\ [][Next \/ Done]_<<seq, i, cand, cnt>>

=============================================================================