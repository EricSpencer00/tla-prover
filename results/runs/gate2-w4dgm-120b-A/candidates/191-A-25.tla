---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 2
ASSUME N \in Nat /\ N >= 2

VARIABLES towers

vars == <<towers>>

\* Tower k's disks are encoded in a binary sum: bit i (2^i) means the i-th
\* size disk is present on that tower. Conservation is a plain integer sum.
RECURSIVE SumF(_)
SumF(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumF(S \ {x})

Total == 2 ^ D - 1

Init ==
  /\ towers = [k \in 0..(N - 1) |-> IF k = 0 THEN Total ELSE 0]
  /\ UNCHANGED towers

\* Only the smallest disk on its source tower may be moved, and never onto a
\* smaller disk on the destination tower.
Move(disk, src, dst) ==
  /\ src # dst
  /\ towers[src] >= disk
  /\ (towers[src] % (disk * 2)) = disk
  /\ towers[dst] % (disk * 2) = 0
  /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
  \/ \E disk \in {1} \cup {2 ^ k : k \in 1..(D - 1)}
       \E src \in 0..(N - 1), dst \in 0..(N - 1) : Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK == \A k \in 0..(N - 1) : towers[k] \in 0..Total

Inv == SumF(0..(N - 1)) = Total

====