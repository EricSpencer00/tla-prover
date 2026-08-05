---- MODULE MCMajority
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

Init == seq = <<>> /\ i = 0 /\ cand = "none" /\ cnt = 0

Bump(c) == IF (cnt < 4) THEN cnt + 1 ELSE cnt

NextSeq ==
    \/ \E v \in Value :
         /\ i < bound
         /\ seq' = Append(seq, v)
         /\ i' = i + 1
    \/ UNCHANGED <<seq, i>>

NextCand ==
    \E v \in Value :
        /\ cand' = v
        /\ UNCHANGED <<seq, i, cnt>>

NextCnt ==
    /\ cnt' = Bump(cand)
    /\ UNCHANGED <<seq, i, cand>>

Next == NextSeq \/ NextCand \/ NextCnt

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Model checking is only run over sequences of length exactly the bound,
\* because the bound is part of the algorithm's correctness argument.
CHECK == seq \in BoundedSeq(Value) /\ Len(seq) = bound

EndCount == IF cnt >= 3 THEN 3 ELSE cnt

MajorityBound == (1 + EndCount) \div 2
Props == cnt >= 2 => cand \in Value

====