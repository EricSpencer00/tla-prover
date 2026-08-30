---- MODULE Hanoi ----
EXTENDS Integers, FiniteSets

CONSTANTS D, N

\* Bits of a natural number encode which disk sizes are present on a tower.
\* NatMask(k) = 2^k, the power-of-two value of the k-th disk.
NatMask(k) == 2 ^ k
AllMask == 2 ^ D - 1

Towers == 0 .. N - 1
Disks == 1 .. (2 ^ D - 1)
Clamped(k) == IF k <= Disks THEN k ELSE Disks

VARIABLES tower

vars == <<tower>>

RECURSIVE SumOver(_)
SumOver(S) == IF S = {} THEN 0
              ELSE LET t == CHOOSE x \in S : TRUE
                   IN tower[t] + SumOver(S \ {t})

TypeOK ==
  /\ tower \in [Towers -> 0 .. AllMask]
  /\ SumOver(Towers) = AllMask

Init ==
  /\ tower = [t \in Towers |-> IF t = 0 THEN AllMask ELSE 0]

\* The smallest disk present on a tower is its lowest set bit. Move only that
\* disk, and only onto a tower whose lowest set bit is larger or empty.
Move(d, from, to) ==
  /\ d \in Disks
  /\ from # to
  /\ (tower[from] / NatMask(d)) * NatMask(d) = tower[from]
  /\ (tower[from] % NatMask(d)) = 0
  /\ ((tower[to] % NatMask(d)) = 0) \/ (tower[to] = 0)
  /\ tower' = [tower EXCEPT ![from] = @ - d, ![to] = @ + d]

Next ==
  \E d \in Disks, from \in Towers, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the bitwise encoding is lossless -- no disk is created or lost.
Inv == SumOver(Towers) = AllMask

====