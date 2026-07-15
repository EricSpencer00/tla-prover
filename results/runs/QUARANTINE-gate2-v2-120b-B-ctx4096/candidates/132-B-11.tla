---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [i \in 1..n |-> S[i]] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Include the definitions of the majority algorithm from the external module *)
INSTANCE Majority

(* Initial state: empty sequence, index 1, no candidate, zero count *)
Init ==
    /\ seq = {}
    /\ i = 1
    /\ cand = {}
    /\ cnt = 0

(* Next-state relation: extend the sequence by one element from Value *)
Next ==
    \/ /\ i <= bound
       /\ \E v \in Value :
            /\ seq' = seq \cup {i}
            /\ seq'[i] = v
            /\ i' = i + 1
            /\ cand' = cand
            /\ cnt' = cnt
    \/ /\ i > bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Full behavior specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================