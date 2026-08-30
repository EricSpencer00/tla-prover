---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi with D disks (sizes 1,2,4,...) and N towers, where each
\* tower's value is the bitwise sum of the disks on it. Conservation of the
\* disks is the safety property; the trace to the goal is a liveness witness
\* (NO LIVENESS PROPERTY is asserted here).
CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

AllDisks == 2 ^ D - 1

TypeOK == towers \in [1..N -> 0..AllDisks]

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

\* Move a disk (a power of two) from one tower to another, only if it is the
\* smallest on the source tower and fits on the destination tower.
Move ==
  \E disk \in {2 ^ k : k \in 0..(D - 1)}
    \E src \in 1..N
      \E dst \in 1..N :
        /\ src # dst
        /\ (towers[src] /\ disk) = disk
        /\ (towers[src] % disk) = 0
        /\ (towers[dst] = 0 \/ (towers[dst] % disk) = 0)
        /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next == Move

Spec == Init /\ [][Next]_vars

Conservation == towers[1] + towers[2] + towers[3] = AllDisks

Inv == Conservation
====