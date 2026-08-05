---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Majority == { x \in Value : cnt >= 2 /\ x = cand }

Init ==
    /\ seq = {}
    /\ i = 0
    /\ cand \in Value
    /\ cnt = 0

Vote(v) ==
    /\ i < bound
    /\ v \in Value
    /\ seq' = [seq EXCEPT ![i + 1] = v]
    /\ i' = i + 1
    /\ IF cnt = 0 \/ v = cand THEN cand' = v /\ cnt' = (cnt) + 1
       ELSE cnt' = cnt - 1

Next ==
    \/ \E v \in Value : Vote(v)
    \/ (i >= bound /\ UNCHANGED <<seq, i, cand, cnt>>)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

BoundedConvergence ==
    \A n \in 0 .. bound, s \in BoundedSeq(Value) :
        (i = n /\ seq = s) ~> (i = bound /\ seq = s)

====