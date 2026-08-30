---- MODULE Hanoi ----
EXTENDS Naturals

\* Tower of Hanoi puzzle: disks are powers of two, each tower is a bitmask sum of
\* its disks, and conservation is the total weight of all disks.

CONSTANTS D, N

Towers == 1..N
Disks == { 2 ^ k : k \in 0..(D - 1) }

Total == 2 ^ D - 1

VARIABLES towers

vars == << towers >>

SumOf(f, S) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN 0
       ELSE LET x == CHOOSE y \in T : TRUE IN f[x] + g[T \ { x }]
  IN g[S]

Init ==
  /\ towers = [t \in Towers |-> IF t = 1 THEN Total ELSE 0]
  /\ UNCHANGED << >>

Move(d, from, to) ==
  /\ from # to
  /\ towers[from] >= d
  /\ (towers[from] % (2 * d)) = d
  /\ (towers[to] % (2 * d)) = 0
  /\ towers' = [towers EXCEPT ![from] = @ - d, ![to] = @ + d]
  /\ UNCHANGED << >>

Next ==
  \E d \in Disks, from \in Towers, to \in Towers: Move(d, from, to)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ towers \in [Towers -> 0..Total]
  /\ SumOf(towers, Towers) = Total

Inv == SumOf(towers, Towers) = Total

====