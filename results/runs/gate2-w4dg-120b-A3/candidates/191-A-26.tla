---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower t's value is the sum of the powers of two for the disks on it. A move
\* is legal only when the source tower's smallest present disk is the one
\* being moved, and the destination tower has no smaller disk than that.
\* Conservation of disks is the whole point of the encoding: the sum of all
\* tower values must always be 2^D - 1.

VARIABLES tower

Towers == 1..N
DiskVals == {2 ^ k : k \in 0..(D - 1)}
DiskBits == {2 ^ k : k \in 0..(D - 1)}

TypeOK ==
  /\ tower \in [Towers -> 0..(2 ^ D - 1)]

\* Bottom bit(s) of a non-empty tower's value: the smallest disk(s) present.
LowestBit(x) == x % 2 * (IF x % 2 = 1 THEN 1 ELSE 2 ^ (CHOOSE k \in 0..(D - 1) : (x % 2 ^ (k + 1)) >= 2 ^ k))

Init ==
  /\ tower = [t \in Towers |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]

Move ==
  \E d \in DiskVals, src \in Towers, dst \in Towers :
    /\ src # dst
    /\ (tower[src] \land d) = d
    /\ LowestBit(tower[src]) = d
    /\ (tower[dst] \land (d - 1)) = 0
    /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == Move

\* Conservation: every bit that leaves one tower enters exactly one other.
Inv ==
  /\ TypeOK
  /\ tower[1] + tower[2] + IF N = 3 THEN tower[3] ELSE 0 = 2 ^ D - 1

Spec == Init /\ [][Next]_tower

====