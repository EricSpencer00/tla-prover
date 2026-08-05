---- MODULE MCMajority ----
EXTENDS Integers

CONSTANT A, B, C
ASSUME A = "a" /\ B = "b" /\ C = "c"

BoundedSeq == UNION { [1 .. n -> {A, B, C}] : n \in 0 .. 2 }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

Init ==
    /\ seq = << >>
    /\ i = 0
    /\ cand = "none"
    /\ cnt = 0

Vote ==
    /\ i < 2
    /\ \E x \in {A, B, C} : seq' = Append(seq, x)
    /\ i' = i + 1
    /\ UNCHANGED <<cand, cnt>>

Bump(c) ==
    /\ cand = c
    /\ cnt < 4
    /\ cnt' = cnt + 1
    /\ cand' = cand
    /\ UNCHANGED <<seq, i>>

New(c) ==
    /\ cand = "none"
    /\ cand' = c
    /\ cnt' = 1
    /\ UNCHANGED <<seq, i>>

Reset ==
    /\ cand # "none"
    /\ cand' = "none"
    /\ cnt' = 0
    /\ UNCHANGED <<seq, i>>

Next ==
    \/ Vote
    \/ \E c \in {A, B, C} : Bump(c)
    \/ \E c \in {A, B, C} : New(c)
    \/ Reset

Spec == Init /\ [][Next]_vars

MajorityHolds ==
    \A a, b \in {1, 2, 3} : (cand = a /\ cand = b) => (a = b)
====