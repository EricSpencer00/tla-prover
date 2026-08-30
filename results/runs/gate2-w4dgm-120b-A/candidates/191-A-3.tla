---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower states are encoded as the sum of the power-of-two sizes of the disks
\* currently standing on each tower; a bitwise AND checks ordering constraints.
\* Conservation is per-bit: the sum over all towers must stay exactly 2^D - 1.

VARIABLES towers

vars == <<towers>>

TypeOK == /\ towers \in [1..N -> 0..(2^D - 1)]
          /\ towers[1] = 2^D - 1
          /\ \A t \in 2..N : towers[t] = 0

\* Conservation: the sum of all tower values is always the full set of disks.
Conservation == (towers[1] + towers[2] + towers[3]) = 2^D - 1

\* Goal reached: all disks stacked on the last tower.
Goal == towers[N] = 2^D - 1

Init == TypeOK /\ ~Goal

\* Moves are driven by three premises: source has the disk, the disk is the
\* smallest on the source, and the destination has no smaller disk.
Move(d, src, dst) ==
    /\ src # dst
    /\ towers[src] >= d
    /\ towers[src] % (2 * d) = d
    /\ towers[dst] % (2 * d) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in {1 << k : k \in 1..D} : \E src \in 1..N, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* No liveness property: we verify the solution by checking the negation of
\* the goal as an invariant; a counterexample trace is the solution.
Inv == Conservation /\ ~Goal
====