---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT D, N

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
DiskValues == { 2 ^ i : i \in 0..(D - 1) }

DiskSet == 1 .. D    \* disk indices, with 1 being the smallest

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES towers

\* Each tower holds a natural number whose binary bits encode the disks
\* present on that tower.  The least‑significant bit corresponds to the
\* smallest disk (disk 1).
\* The collection `towers` is a function that maps each tower index (1..N)
\* to its current value.
\* ----------------------------------------------------------------------
vars == << towers >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The value that represents all disks stacked together.
AllDisks == 2 ^ D - 1

\* The bit mask for a particular disk index i (i ∈ DiskSet).
Mask(i) == 2 ^ (i - 1)

\* Returns the smallest disk that is present on tower t.
SmallestDisk(t) ==
  IF towers[t] = 0 THEN 0
  ELSE CHOOSE i \in DiskSet : (towers[t] /\ Mask(i)) # 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Type correctness invariant (required identifier: TypeOK)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ towers \in [1..N -> Nat]
  /\ \A i \in 1..N : towers[i] < 2 ^ D

\* ----------------------------------------------------------------------
\* Move action (the only possible evolution step)
\* ----------------------------------------------------------------------
Move ==
  \E src \in 1..N, dst \in 1..N :
    /\ src # dst
    /\ towers[src] # 0
    /\ LET d == SmallestDisk(src) IN
        /\ d # 0                                   \* a disk is present
        /\ (towers[src] /\ Mask(d)) # 0            \* d is indeed on src
        /\ towers[dst] = 0 \/ (towers[dst] /\ Mask(d)) = 0
           \* destination empty or does not contain a smaller disk
        /\ towers' = [towers EXCEPT
                       ![src] = towers[src] - Mask(d),
                       ![dst] = towers[dst] + Mask(d)]

\* ----------------------------------------------------------------------
\* Next-state relation (required identifier: Next)
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Full specification (required identifier: Spec)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant (required identifier: Inv)
\* ----------------------------------------------------------------------
Inv ==
  /\ /\ \A i \in 1..N : towers[i] \in Nat
     /\ \A i \in 1..N : towers[i] < 2 ^ D
  /\ \A i, j \in 1..N :
        i # j => (towers[i] /\ towers[j]) = 0
  /\ \A i \in 1..N :
        (towers[i] = 0) \/ 
        (LET s == SmallestDisk(i) IN s # 0 /\ 
         \A k \in DiskSet : k # s => (Mask(k) /\ towers[i]) = 0)

\* ----------------------------------------------------------------------
\* The specification declares the identifiers required by the .cfg file.
\* ----------------------------------------------------------------------
====