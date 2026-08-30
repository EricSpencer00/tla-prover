---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

\* Tower values are binary encodings of which power-of-two-sized disks sit on them.
\* Conservation (sum == 2^D - 1) is the only thing keeping disk count intact.

VARIABLES towers

vars == <<towers>>

RECURSIVE SumOver(_)
SumOver(S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumOver(S \ {x})

OnDisk(disk) == \E t \in 1..N : towers[t] % (2 * disk) >= disk

Init ==
    /\ towers = [t \in 1..N |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]
    /\ UNCHANGED << >>

Move(disk, src, dst) ==
    /\ src # dst
    /\ towers[src] % (2 * disk) >= disk
    /\ towers[dst] % (2 * disk) < disk
    /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]
    /\ UNCHANGED << >>

Next ==
    \E disk \in { 2 ^ k : k \in 0..(D - 1) } : \E src \in 1..N, dst \in 1..N : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK == \A t \in 1..N : towers[t] \in 0..(2 ^ D - 1)

Inv == SumOver(1..N) = 2 ^ D - 1

Goal == towers[N] = 2 ^ D - 1
====