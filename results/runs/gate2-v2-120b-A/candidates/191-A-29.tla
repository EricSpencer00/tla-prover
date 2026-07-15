---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

CONSTANT D, N

\* Derived constants
DiskVals == { 2 ^ i : i \in 0..(D-1) }
AllDisks == UNION DiskVals
AllMask == 2 ^ D - 1          \* All bits set for the D disks

VARIABLES towers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DiskLessThan(d) == { d2 \in DiskVals : d2 < d }

\* towers[i] is the bitmask of disks currently on tower i (1..N)
TowerRange == 1..N

\* The mask of the smallest disk present on a tower (or 0 if empty)
SmallestDisk(t) ==
  IF towers[t] = 0 THEN 0
  ELSE 2 ^ Min({ i \in 0..(D-1) : (towers[t] & (2 ^ i)) # 0 })

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ towers = [i \in TowerRange |-> IF i = 1 THEN AllMask ELSE 0]

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
  \E i, j \in TowerRange :
    /\ i # j
    /\ LET srcMask   == towers[i] IN
       LET dstMask   == towers[j] IN
       LET sd        == SmallestDisk(i) IN
       /\ sd # 0                                   \* there is a disk to move
       /\ (srcMask & sd) = sd                      \* sd is actually on source
       /\ (dstMask & (sd - 1)) = 0                 \* no smaller disk on dest
       /\ towers' = [t \in TowerRange |-> 
                      IF t = i THEN srcMask - sd
                      ELSE IF t = j THEN dstMask + sd
                      ELSE towers[t]]

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock
\* ----------------------------------------------------------------------
Stutter == UNCHANGED towers

Next == Move \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* ----------------------------------------------------------------------
\* Safety properties (invariants)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ towers \in [TowerRange -> Nat]
  /\ \A i \in TowerRange : towers[i] \in 0..AllMask
  /\ \A i \in TowerRange :
        \A d \in DiskVals :
          (towers[i] & d) # 0 => \A e \in DiskLessThan(d) :
                                   (towers[i] & e) = 0

Inv ==
  /\ \A i \in TowerRange : towers[i] \in 0..AllMask
  /\ \A i \in TowerRange :
        \A d \in DiskVals :
          (towers[i] & d) # 0 => \A e \in DiskLessThan(d) :
                                   (towers[i] & e) = 0
  /\ \Sum_{i \in TowerRange} towers[i] = AllMask

=============================================================================