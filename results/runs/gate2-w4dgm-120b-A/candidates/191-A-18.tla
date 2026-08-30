---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* The position of every disk on the Tower of Hanoi is encoded in one value per
\* tower: the k-th bit of a tower value tells whether the disk of size 2^k sits
\* on that tower.  A move removes one disk from a source tower and adds it to a
\* destination tower.
VARIABLES p

vars == <<p>>

Towers == 0 .. (N - 1)
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOver(f, S \ {x})

TypeOK == /\ p \in [Towers -> 0 .. (2 ^ D) - 1]
          /\ SumOver(p, Towers) = (2 ^ D) - 1

Init == /\ p = [t \in Towers |-> IF t = 0 THEN (2 ^ D) - 1 ELSE 0]

\* A legal move: the disk is on the source, is the smallest on that source,
\* and is not bigger than the smallest on the destination -- so a larger disk
\* is never placed on top of a smaller one.
Move(d, s, t) ==
  /\ s # t
  /\ p[s] % (d * 2) = d
  /\ (p[t] = 0 \/ p[t] % (d * 2) = 0)
  /\ p' = [p EXCEPT ![s] = @ - d, ![t] = @ + d]

Next == \E d \in Disks, s \in Towers, t \in Towers : Move(d, s, t)

Spec == Init /\ [][Next]_vars

\* Conservation: the three towers always account for exactly the starting set
\* of disks, no matter how they are shuffled.
Inv == SumOver(p, Towers) = (2 ^ D) - 1

====