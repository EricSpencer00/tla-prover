---- MODULE MCMajority -------------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS bound

(* The set of possible values that may appear in the sequence. *)
Value == {1, 2, 3}

(* All sequences (functions from a prefix of 1..bound to Value). *)
SeqSet == { s \in [1..bound -> Value] : 
              \A i \in 1..bound : (i \in DOMAIN s) => s[i] \in Value }

VARIABLES seq, i, cand, cnt

(* ------------------------------------------------------------------------- *)
(* The Majority algorithm (Boyer–Moore)                                       *)
(* ------------------------------------------------------------------------- *)

AlgAction ==
    /\ i < bound
    /\ i' = i + 1
    /\ IF cnt = 0
          THEN /\ cand' = seq[i + 1]
               /\ cnt' = 1
          ELSE IF seq[i + 1] = cand
                  THEN /\ cnt' = cnt + 1
                       /\ cand' = cand
                  ELSE /\ cnt' = cnt - 1
                       /\ cand' = cand

Next == AlgAction

(* Initial state: an arbitrary allowed sequence, counters at start. *)
Init ==
    /\ seq \in SeqSet
    /\ i = 0
    /\ cnt = 0
    /\ cand \in Value

vars == <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* The invariant states that there is at most one element that can be a      *)
(* majority (appears more than half the time).                               *)
(* ------------------------------------------------------------------------- *)

MajorityInvariant ==
    \A v \in Value :
        (\A j \in 1..bound : seq[j] = v) => cnt > 0 /\ cand = v

=============================================================================