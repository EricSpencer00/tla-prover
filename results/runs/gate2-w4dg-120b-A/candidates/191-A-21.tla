---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

ASSUME D \in Nat /\ D >= 1
ASSUME N \in Nat /\ N >= 2

\* Tower values encode disk presence as a summed set of powers of two.
VARIABLES towers

vars == <<towers>>

SumTowerVals == towers[1] + towers[2] + ... + towers[N]
GoalMask == (2 ^ D) - 1

TypeOK ==
  /\ towers \in [1..N -> 0..GoalMask]

\* Conservation: the total summed mask never changes.
Inv ==
  /\ SumTowerVals = GoalMask
  /\ TypeOK

DiskOn(t, k) == (towers[t] \land (2 ^ k)) = (2 ^ k)

MinDiskOn(t) ==
  CHOOSE k \in 0..(D - 1) : DiskOn(t, k) /\ \A j \in 0..(k - 1) : ~DiskOn(t, j)

Init ==
  /\ towers = [t \in 1..N |-> IF t = 1 THEN GoalMask ELSE 0]
  /\ TypeOK

Move(disk, src, dst) ==
  /\ src # dst
  /\ (towers[src] \land disk) = disk
  /\ disk = MinDiskOn(src)
  /\ (towers[dst] = 0 \/ (towers[dst] \land (disk - 1)) = 0)
  /\ towers' = [towers EXCEPT ![src] = towers[src] - disk, ![dst] = towers[dst] + disk]
  /\ TypeOK

Next ==
  \/ \E k \in 0..(D - 1), s \in 1..N, d \in 1..N : Move(2 ^ k, s, d)
  \/ UNCHANGED towers

Spec == Init /\ [][Next]_vars

====