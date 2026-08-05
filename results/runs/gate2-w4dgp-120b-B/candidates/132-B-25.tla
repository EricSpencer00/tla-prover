---- MODULE MCMajority ----
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt
vars == <<seq, i, cand, cnt>>

INSTANCE Majority

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 0 .. bound
    /\ cand \in Value
    /\ cnt \in 0 .. bound

Init ==
    /\ seq = [n \in (1 .. bound) |-> A]
    /\ i = 0
    /\ cand = A
    /\ cnt = 0

Next ==
    \/ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
       /\ cand' = IF cnt = 0 THEN seq[i + 1] ELSE cand
       /\ UNCHANGED <<seq, i>>
    \/ i' = i + 1
       /\ UNCHANGED <<seq, cand, cnt>>

Next2 ==
    \E j \in 0 .. bound - 1 :
        /\ i = j
        /\ \/ cnt' = IF cnt = 0 THEN 1 ELSE cnt + 1
              /\ cand' = IF cnt = 0 THEN seq[j + 1] ELSE cand
              /\ UNCHANGED <<seq>>
           \/ i' = i + 1
              /\ UNCHANGED <<seq, cand, cnt>>

Spec == Init /\ [][Next]_vars
Spec2 == Init /\ [][Next2]_vars
====