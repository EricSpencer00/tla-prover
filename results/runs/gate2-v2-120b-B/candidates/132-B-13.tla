---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

CONSTANTS A, B, C, bound

(* The three possible values are those three distinct constants *)
Value == {A, B, C}

(* A sequence over a set S of length n is a function from 1..n to S.
   The empty sequence is represented by the empty function. *)
SeqOf(S) ==
  UNION { [i \in 1..n |-> v] : n \in 0..bound, v \in [1..n -> S] }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 0, no candidate, zero count *)
Init ==
  /\ seq = {}
  /\ i = 0
  /\ cand = NULL
  /\ cnt = 0

(* One step of the majority‑vote algorithm, operating on the next element   *)
Step ==
  /\ i < bound
  /\ \E x \in Value :
        /\ i' = i + 1
        /\ seq' = [seq EXCEPT ![i'] = x]
        /\ IF cnt = 0 THEN
               /\ cand' = x
               /\ cnt'  = 1
           ELSE IF cand = x THEN
               /\ cand' = cand
               /\ cnt'  = cnt + 1
           ELSE
               /\ cand' = cand
               /\ cnt'  = cnt - 1

Next == Step

(* The specification of the algorithm *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================