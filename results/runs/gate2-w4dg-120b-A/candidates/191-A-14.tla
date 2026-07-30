---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower k's value is a bitwise encoding of the disks on it: bit j set
\* means the disk of size 2^j is present. Disks themselves are powers of 2.
Disk(j) == 2 ^ j

Towers == 0 .. (N - 1)
AllDisks == 2 ^ D - 1
HighestBit == 1 << (D - 1)

VARIABLES tower
vars == <<tower>>

Bump == [k \in Towers |-> IF k = 0 THEN AllDisks ELSE 0]

TypeOK ==
  /\ tower \in [Towers -> 0 .. AllDisks]
  /\ tower[0] = AllDisks + Bump[0]
  /\ \A k \in Towers : tower[k] =< AllDisks

Init == tower = Bump

\* A disk is movable if it is present and is the smallest disk on its
\* tower (no smaller bit set). Dest must be empty or have no smaller disk.
Move(d, from, to) ==
  /\ from # to
  /\ d <= HighestBit
  /\ (tower[from] /\ d) = d
  /\ (tower[from] % d) = 0
  /\ (tower[to] = 0 \/ (tower[to] % d) = 0)
  /\ tower' = [tower EXCEPT ![from] = @ - d, ![to] = @ + d]

Next == \E d \in {Disk(j) : j \in 0 .. (D - 1)} : \E from, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the sum of all tower values is always the total weight of
\* every disk together, so disks are never created or destroyed.
Inv == LET Sum[S \in SUBSET Towers] ==
           IF S = {} THEN 0
           ELSE LET k == CHOOSE x \in S : TRUE IN tower[k] + Sum[S \ {k}]
        IN Sum[Towers] = AllDisks

====