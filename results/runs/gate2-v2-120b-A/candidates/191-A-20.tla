---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskVals == { 2 ^ k : k \in 0..(D - 1) }

\* ----------------------------------------------------------------------
\* State variable: TowerVals is a function mapping each tower (0..N-1) to a
\* natural number encoding the set of disks on that tower as a bitfield.
\* ----------------------------------------------------------------------
VARIABLES TowerVals

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllDisksMask == 2 ^ D - 1

\* The smallest disk present on a tower t (0 if the tower is empty)
SmallestDisk(t) ==
  IF TowerVals[t] = 0 THEN 0
  ELSE 2 ^ (Min({ k \in 0..(D-1) : (TowerVals[t] \div 2 ^ k) % 2 = 1 }))

\* Disk d is present on tower t
DiskOn(d, t) ==
  (TowerVals[t] \div d) % 2 = 1

\* No disk smaller than d is present on tower t
NoSmaller(d, t) ==
  \A k \in 0..(D-1) :
    (2 ^ k) < d => ((TowerVals[t] \div (2 ^ k)) % 2 = 0)

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ TowerVals = [t \in 0..(N-1) |-> IF t = 0 THEN AllDisksMask ELSE 0]
  /\ \A t \in 0..(N-1): TowerVals[t] \in 0..AllDisksMask

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
  \E d \in DiskVals :
    \E s \in 0..(N-1) :
      \E dst \in 0..(N-1) :
        /\ s # dst
        /\ DiskOn(d, s)
        /\ SmallestDisk(s) = d
        /\ NoSmaller(d, dst)
        /\ TowerVals' = [TowerVals EXCEPT
                          ![s] = TowerVals[s] - d,
                          ![dst] = TowerVals[dst] + d]

Next == Move

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<TowerVals>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ \A t \in 0..(N-1): TowerVals[t] \in 0..AllDisksMask
  /\ \A t \in 0..(N-1): TowerVals[t] = 0 \/ TowerVals[t] \in DiskVals

Inv ==
  /\ \A t \in 0..(N-1): TowerVals[t] \in 0..AllDisksMask
  /\ ( \A d \in DiskVals : \A t1, t2 \in 0..(N-1) :
        (DiskOn(d, t1) /\ DiskOn(d, t2)) => t1 = t2 )
  /\ \A t \in 0..(N-1) :
        (TowerVals[t] # 0) => SmallestDisk(t) = Min({ k \in 0..(D-1) :
                                                    (TowerVals[t] \div 2 ^ k) % 2 = 1 })
  /\ \A t \in 0..(N-1) :
        \A d \in DiskVals :
          DiskOn(d, t) => NoSmaller(d, t)
  /\ \A t \in 0..(N-1) : TowerVals[t] >= 0
  /\ Sum(TowerVals) = AllDisksMask

\* ----------------------------------------------------------------------
\* Theorem (optional, for documentation)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

====