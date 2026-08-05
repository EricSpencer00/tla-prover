---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

Init == seq = << >> /\ i = 0 /\ cand = A /\ cnt = 0
Append(v) == seq' = Append(seq, v) /\ i' = i + 1 /\ UNCHANGED <<cand, cnt>>
Vote == IF cnt = 0 /\ i > 0 THEN cand' = seq[i] /\ cnt' = 1
        ELSE IF i > 0 /\ cand = seq[i] THEN cnt' = cnt + 1
        ELSE IF cnt > 0 THEN cnt' = cnt - 1
        ELSE UNCHANGED <<cand, cnt>> /\ UNCHANGED <<seq, i>>

Next == \E v \in Value : Append(v) \/ Vote

vars == <<seq, i, cand, cnt>>
Spec == Init /\ [][Next]_vars

Invariant == i <= bound
BoundedSeqOk == seq \in BoundedSeq(Value)
====