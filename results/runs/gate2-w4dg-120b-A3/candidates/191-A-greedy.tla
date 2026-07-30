---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ..., 2^(D-1). A tower's value is the
\* sum of the sizes of the disks on it, so its binary representation encodes
\* exactly which disks are present.
Disks == { 2 ^ k : k \in 0 .. (D - 1) }

VARIABLES towers

vars == << towers >>

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ {x})

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]
  /\ SumOf({towers[i] : i \in 1 .. N}) = (2 ^ D) - 1

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* A move is legal only if the disk is the smallest on the source tower and
\* the destination tower has no smaller disk already on it.
Move(d, src, dst) ==
  /\ src # dst
  /\ d \in Disks
  /\ (towers[src] /\ d) = d
  /\ (towers[src] % d) = 0
  /\ (towers[dst] /\ (d - 1)) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \/ \E d \in Disks, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the total number of disks never changes.
Inv == SumOf({towers[i] : i \in 1 .. N}) = (2 ^ D) - 1

====