---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Disks == { 2 ^ k : k \in 0 .. (D - 1) }

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ { x })

ASSUME SumOf(Disks) = 2 ^ D - 1

VARIABLES towers

vars == << towers >>

TypeOK ==
  /\ towers \in [1 .. N -> 0 .. (2 ^ D) - 1]
  /\ SumOf(ranges(towers)) = 2 ^ D - 1

Init ==
  /\ towers = [i \in 1 .. N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

Inv == towers[N] = 2 ^ D - 1

Move(d, src, dst) ==
  /\ src # dst
  /\ towers[src] >= d
  /\ towers[src] % (2 * d) = d
  /\ towers[dst] % (2 * d) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
  \E d \in Disks, src, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

====