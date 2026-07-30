---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

\* Disk k has size 2^k; a tower's value is the sum of sizes of the disks on it,
\* so the binary representation of the value encodes exactly which disks are
\* present. The bitwise AND test below is what makes the "top-of-stack" check
\* well-defined for this encoding.
CONSTANTS D, N

\* Powers of two for each disk size; indexing starts at 1 because the tower
\* values are 1-indexed (tower 1 has all disks initially).
Disks == {2 ^ k : k \in 0 .. (D - 1)}

Towers == 1 .. N
Bits == {2 ^ k : k \in 0 .. (D - 1)}
LastTower == N

VARIABLES towers

vars == <<towers>>

TypeOK == /\ towers \in [Towers -> 0 .. (2 ^ D) - 1]
          /\ towers[LastTower] \in 0 .. (2 ^ D) - 1

Conservation == towers[1] + towers[2] + towers[LastTower]
                = (2 ^ D) - 1

\* The source tower's smallest disk must be the one being moved: all strictly
\* smaller bits are zero. The destination tower must have no smaller disk, or
\* be empty, so the move never places a large disk on top of a smaller one.
Move(d, from, to) ==
    /\ d \in Disks
    /\ from \in Towers
    /\ to \in Towers
    /\ from # to
    /\ (towers[from] /\ d) = d
    /\ \A b \in Bits : b < d => ((towers[from] /\ b) = 0)
    /\ \A b \in Bits : b < d => ((towers[to] /\ b) = 0)
    /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]

Init ==
    /\ towers[1] = (2 ^ D) - 1
    /\ towers[2] = 0
    /\ towers[LastTower] = 0

Next == \E d \in Disks, from \in Towers, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* No explicit liveness: the puzzle is "solved" by showing the negation of the
\* goal state is an invariant.
Inv == towers[LastTower] # (2 ^ D) - 1

====