---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

\* D and N are declared as constants in the .cfg file; the module must not
\* assign them, only use their values.
CONSTANTS
  D
  N

\* TowerValues encodes which disks are present on each tower via a single
\* natural number whose binary representation has one bit per disk size.
VARIABLES
  TowerValues

vars == <<TowerValues>>

\* The sum of all tower values always equals 2^D - 1.  Because each tower
\* value is the sum of its disks' powers of two, towers are disjoint and the
\* total is fixed once and for all.
RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

RECURSIVE OnStack(_, _, _)
\* OnStack(k, t, T) is TRUE iff disk k is the smallest (topmost) disk on tower t.
OnStack(k, t, T) ==
  ((T[t] \div 2^k) % 2) = 1
    /\ (\A j \in 0 .. (k - 1) : ((T[t] \div 2^j) % 2) = 0)

RECURSIVE CanPlace(_, _)
\* CanPlace(k, t) is TRUE iff tower t has no disk smaller than disk k.
CanPlace(k, t) ==
  (\A j \in 0 .. (k - 1) : ((TowerValues[t] \div 2^j) % 2) = 0)

\* The puzzle starts with all disks on tower 0.
Init ==
  /\ TowerValues = [t \in 0 .. (N - 1) |-> IF t = 0 THEN 2^D - 1 ELSE 0]

\* A single move of one disk, in the only order that ever moves it.
Move(disk, src, dst) ==
  /\ src # dst
  /\ src \in 0 .. (N - 1)
  /\ dst \in 0 .. (N - 1)
  /\ disk \in {2^k : k \in 0 .. (D - 1)}
  /\ ((TowerValues[src] \div disk) % 2) = 1
  /\ (\E k \in 0 .. (D - 1) : disk = 2^k /\ OnStack(k, src, TowerValues))
  /\ CanPlace(disk, dst)
  /\ TowerValues' = [TowerValues EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
  \E disk \in {2^k : k \in 0 .. (D - 1)}:
    \E src \in 0 .. (N - 1):
      \E dst \in 0 .. (N - 1):
        Move(disk, src, dst)

TypeOK ==
  /\ TowerValues \in [0 .. (N - 1) -> 0 .. (2^D - 1)]
  /\ SumOver(TowerValues, 0 .. (N - 1)) = 2^D - 1

\* Conservation: the number of disks never changes.  Every move takes one
\* disk from a source tower and puts exactly one on a destination tower.
Inv ==
  SumOver(TowerValues, 0 .. (N - 1)) = 2^D - 1

Spec == Init /\ [][Next]_vars

====