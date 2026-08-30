---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

RECURSIVE SumTowers(_)
SumTowers(S) ==
    IF S = {} THEN 0
    ELSE LET t == CHOOSE x \in S : TRUE
         IN towers[t] + SumTowers(S \ {t})

RECURSIVE BitsBelow(_)
BitsBelow(k) == IF k = 0 THEN 0 ELSE 2 ^ (k - 1) + BitsBelow(k - 1)

TypeOK ==
    /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]
    /\ towers[1] = (2 ^ D) - 1
    /\ \A t \in 1 .. N : towers[t] >= 0

Init ==
    /\ towers = [t \in 1 .. N |-> IF t = 1 THEN (2 ^ D) - 1 ELSE 0]

Move(disk, src, dest) ==
    /\ src # dest
    /\ src \in 1 .. N
    /\ dest \in 1 .. N
    /\ disk \in {2 ^ k : k \in 0 .. D - 1}
    /\ towers[src] >= disk
    /\ towers[src] % (2 * disk) = disk
    /\ towers[dest] % (2 * disk) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dest] = @ + disk]

Next ==
    \E disk \in {2 ^ k : k \in 0 .. D - 1} :
        \E src, dest \in 1 .. N :
            Move(disk, src, dest)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ SumTowers(1 .. N) = (2 ^ D) - 1
    /\ TypeOK
====