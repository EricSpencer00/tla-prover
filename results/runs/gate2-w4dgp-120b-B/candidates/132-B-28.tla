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

Init ==
  /\ seq = [1..bound |-> A]
  /\ i = 1
  /\ cand = A
  /\ cnt = 1

Step ==
  /\ i < bound
  /\ \E x \in Value :
       /\ seq' = [seq EXCEPT ![i+1] = x]
       /\ i' = i + 1
       /\ cand' = IF cnt = 0 THEN x ELSE cand
       /\ cnt' = IF x = cand THEN cnt + 1 ELSE cnt - 1

Result ==
  /\ \E j \in 1..i : seq[j] = cand
  /\ UNCHANGED <<seq, i, cand, cnt>>

Spec == Init /\ [][Step]_<<seq, i, cand, cnt>> /\ WF_vars(Step) /\ WF_vars(Result)
====