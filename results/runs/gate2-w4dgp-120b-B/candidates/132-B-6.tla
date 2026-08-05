---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

VARIABLES seq, i, cand, cnt

Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand = 0
    /\ cnt = 0

Step ==
    /\ i < bound
    /\ \E x \in Value :
         /\ seq' = [seq EXCEPT ![i + 1] = x]
         /\ cand' = IF (i = 0)\/(x = cand) THEN x ELSE (IF cnt > 1 THEN cand ELSE 0)
         /\ cnt' = IF i = 0 THEN 1 ELSE (IF x = cand THEN cnt + 1 ELSE cnt - 1)
    /\ i' = i + 1

Next == Step

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

Bounded == Cardinality(seq) <= bound

====