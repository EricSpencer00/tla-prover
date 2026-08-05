---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

Next == (i < Len(seq)) /\ cand' = seq[i + 1] /\ cnt' = 1 /\ i' = i + 1
        \/ (i >= Len(seq)) /\ i' = 0 /\ cand' = cand /\ cnt' = cnt
        \/ (i < Len(seq) /\ seq[i + 1] = cand) /\ cnt' = cnt + 1 /\ i' = i + 1 /\ cand' = cand
        \/ (i < Len(seq) /\ seq[i + 1] # cand /\ cnt = 1) /\ cnt' = 0 /\ i' = i + 1 /\ cand' = seq[i + 1]

StateConstraint == cand \in Value

vars == <<seq, i, cand, cnt>>

Spec == Init /\ [][Next]_vars

====