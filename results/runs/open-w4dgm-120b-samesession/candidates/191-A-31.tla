---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

Mask(v) == 2 ^ D - 1

RECURSIVE SumTowers(_)
SumTowers(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN towers[x] + SumTowers(S \ {x})

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]
    /\ UNCHANGED towers

Move(d, s, t) ==
    /\ s # t
    /\ d \in 1 .. (2 ^ D) - 1
    /\ d * 2 <= (2 ^ D)
    /\ (towers[s] /\ d) = d
    /\ (towers[s] % (2 * d)) = d
    /\ (towers[t] % (2 * d)) = 0
    /\ towers' = [towers EXCEPT ![s] = @ - d, ![t] = @ + d]

Next ==
    \E d \in 1 .. (2 ^ D) - 1, s \in 1..N, t \in 1..N : Move(d, s, t)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ towers \in [1..N -> 0 .. (2 ^ D) - 1]
    /\ \A i \in 1..N : towers[i] = 0 \/ towers[i] \in (Nat \ {0})
    /\ \A i \in 1..N : towers[i] <= (2 ^ D) - 1

Inv ==
    /\ SumTowers(1..N) = (2 ^ D) - 1
    /\ TypeOK
====