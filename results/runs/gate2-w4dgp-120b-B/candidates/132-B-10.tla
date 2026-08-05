---- MODULE MCMajority -------------------------------------------------
EXTENDS Naturals, FiniteSets, Majority
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == { f \in [1 .. bound -> S] : TRUE }

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

Init ==
    /\ seq = {}
    /\ i = 1
    /\ cand = A
    /\ cnt = 0

Vote(v) ==
    /\ seq' = [seq EXCEPT ![i] = v]
    /\ i' = i + 1
    /\ cand' = IF cnt = 0 THEN v ELSE cand
    /\ cnt' = IF cnt = 0 THEN 1 ELSE IF v = cand THEN cnt + 1 ELSE cnt - 1

Next == \E v \in Value : Vote(v)

Spec == Init /\ [][Next]_vars

Inv == i \in 1 .. (bound + 1)
=============================================================================