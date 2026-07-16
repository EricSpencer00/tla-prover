------------------------------ MODULE MCMajority ---------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* The bound must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* A bounded sequence of elements drawn from S, with length up to `bound`. *)
BoundedSeq(S) == 
  UNION { [i \in 1..n |-> S[i]] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Initialization: start with the empty sequence and default candidate/counter. *)
Init ==
  /\ seq = {}
  /\ i = 0
  /\ cand \in Value \cup {Null}
  /\ cnt = 0

(* Extend the sequence by one element from Value, updating the Boyer‑Moore state. *)
Next ==
  \/ /\ i < bound
     /\ \E e \in Value :
          /\ seq' = seq \cup {[i + 1 |-> e]}
          /\ i' = i + 1
          /\ IF cnt = 0
                THEN /\ cand' = e
                     /\ cnt' = 1
                ELSE IF e = cand
                        THEN /\ cand' = cand
                             /\ cnt' = cnt + 1
                        ELSE /\ cand' = cand
                             /\ cnt' = cnt - 1
  \/ /\ i = bound
     /\ UNCHANGED <<seq, i, cand, cnt>>

(* The system always stays within the bounded domain. *)
Domain ==
  /\ seq \in BoundedSeq(Value)
  /\ i \in 0..bound
  /\ cand \in Value \cup {Null}
  /\ cnt \in Nat

(* The overall specification. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================