---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm over three     *)
(* elements of bounded length, using Majority.tla's BoundedMajority0.         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt
vars == << seq, i, cand, cnt >>

Init ==
  /\ seq = << >>
  /\ i = 0
  /\ cand = "none"
  /\ cnt = 0

New ==
  /\ i < bound
  /\ \E x \in Value :
       /\ seq' = [seq EXCEPT ![i + 1] = x]
       /\ i' = i + 1
  /\ UNCHANGED << cand, cnt >>

Majority == BoundedMajority0(seq)

Next == New \/ Majority

Spec == Init /\ [][Next]_vars

BothSpec == Spec /\ BoundedMajority0(seq)
=============================================================================