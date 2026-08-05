---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \notin Nat

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

Majority(s) == CHOOSE v \in Value :
    3 * Cardinality({ k \in DOMAIN s : s[k] = v }) > Cardinality(DOMAIN s)

Init ==
    /\ seq = << >>
    /\ i = 1
    /\ cand = A
    /\ cnt = 0

Append ==
    /\ i <= bound
    /\ \E x \in Value :
        /\ seq' = [seq EXCEPT ![i] = x]
        /\ cand' = IF cnt = 0 \/ cand = x THEN x ELSE cand
        /\ cnt' = IF cnt = 0 \/ cand = x THEN cnt + 1 ELSE cnt - 1
    /\ i' = i + 1

Check ==
    /\ i > bound
    /\ cand = Majority(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Append \/ Check

vars == <<seq, i, cand, cnt>>
Spec == Init /\ [][Next]_vars

Bounded == (i > bound) ~> (i > bound)
MajorityExists == <>(cand = Majority(seq))
====