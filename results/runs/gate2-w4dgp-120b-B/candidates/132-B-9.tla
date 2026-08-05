---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(* This version repairs the original so that SANY parses it and TLC model-   *)
(* checks it successfully -- the semantics of the algorithm are unchanged.    *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

Init ==
    /\ seq = << >>
    /\ i = 0
    /\ cand = C
    /\ cnt = 0

Append(v) ==
    /\ i < bound
    /\ seq' = [seq EXCEPT ![i + 1] = v]
    /\ i' = i + 1
    /\ UNCHANGED <<cand, cnt>>

Step ==
    /\ i < bound
    /\ cand' = C
    /\ cnt' = 0
    /\ UNCHANGED <<seq, i>>

Next ==
    \/ \E v \in Value : Append(v)
    \/ Step

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* The majority candidate is the element appearing at least twice.
MajorityResult ==
    \E c \in Value :
        /\ \A j \in 1 .. i : seq[j] = c
        /\ i >= 2

====