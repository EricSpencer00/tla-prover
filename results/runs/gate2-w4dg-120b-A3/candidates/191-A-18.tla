---- MODULE Hanoi ----
\* Tower of Hanoi puzzle modelled as a bitwise distribution of disk values across towers.
\* Each tower's value is the sum of the disk values it currently holds; disk values are
\* powers of two so the bits of that sum encode the exact set of disks on the tower.
EXTENDS Naturals

CONSTANTS D, N

Disks == { 2 ^ k : k \in 0 .. (D - 1) }
TopDisk == 2 ^ (D - 1)

VARIABLES towers, moves
vars == <<towers, moves>>

TowerSum == towers[1] + towers[2] + towers[3]

\* A disk is present on a tower if its bit is set in that tower's value.
IsPresent(d, k) == (towers[k] / d) % 2 = 1

\* A disk is the smallest disk on a tower if it is present and no smaller disk is.
IsSmallest(d, k) == IsPresent(d, k) /\ \A e \in Disks : e < d => ~IsPresent(e, k)

\* A tower has no disk smaller than d if no such disk is present on it.
NoSmaller(d, k) == \A e \in Disks : e < d => ~IsPresent(e, k)

Init ==
  /\ towers = [k \in 1 .. N |-> IF k = 1 THEN (2 ^ D) - 1 ELSE 0]
  /\ moves = 0

\* Single legal move of one disk from one tower to another.
Move(d, src, dst) ==
  /\ src # dst
  /\ src \in 1 .. N
  /\ dst \in 1 .. N
  /\ IsPresent(d, src)
  /\ IsSmallest(d, src)
  /\ NoSmaller(d, dst)
  /\ towers' = [k \in 1 .. N |-> IF k = src THEN towers[k] - d ELSE IF k = dst THEN towers[k] + d ELSE towers[k]]
  /\ moves' = moves + 1

Next == \E d \in Disks, src \in 1 .. N, dst \in 1 .. N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: every disk is accounted for exactly once across all towers.
TypeOK == TowerSum = (2 ^ D) - 1

\* All tower values stay within the representable range.
Inv == \A k \in 1 .. N : towers[k] \in 0 .. ((2 ^ D) - 1)

====