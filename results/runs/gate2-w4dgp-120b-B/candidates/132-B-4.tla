---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

vars == <<seq, i, cand, cnt>>

Init ==
  /\ seq = [1 .. bound -> Value]
  /\ i = 0
  /\ cand = A
  /\ cnt = 0

Vote ==
  /\ i < bound
  /\ i' = i + 1
  /\ IF seq[i + 1] = cand Then cnt' = cnt + 1
     ELSE IF cnt <= 0 THEN cand' = seq[i + 1] /\ cnt' = 1
     ELSE cnt' = cnt - 1
  /\ UNCHANGED <<seq, cand>>

Next == Vote

Spec == Init /\ [][Next]_vars

Result == IF cnt > 0 THEN cand ELSE "none"
=============================================================================