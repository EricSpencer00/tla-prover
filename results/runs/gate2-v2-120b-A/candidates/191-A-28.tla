---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANT D, N

\* -----------------------------------------------------------------
\* Derived sets
\* -----------------------------------------------------------------
Disk == { i \in 1..D }               \* indices of disks (1 = smallest)
DiskVal == { 2^(i-1) : i \in Disk }  \* actual size values (powers of two)

TowerIdx == 1..N

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES towers

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
(* The total sum of all disks, used for the conservation invariant. *)
Total == 2^D - 1

(* Convert a tower's numeric encoding to the set of disks it currently holds. *)
TowerSet(t) == { i \in Disk : (t \div 2^(i-1)) % 2 = 1 }

(* The smallest disk present on a tower, expressed as its size value.
   Returns 0 iff the tower is empty. *)
MinDisk(t) ==
  IF t = 0 THEN 0
  ELSE 2^(MinSet(t)-1)

(* The index (1..D) of the smallest disk on a tower, or 0 if empty. *)
MinSet(t) ==
  IF t = 0 THEN 0
  ELSE
    CHOOSE i \in Disk :
      (t \div 2^(i-1)) % 2 = 1 /\ 
      \A j \in Disk : j < i => (t \div 2^(j-1)) % 2 = 0

(* A disk value d is present on tower t iff d is a power of two that appears
   in the binary representation of t. *)
DiskOn(d, t) == (t \div d) % 2 = 1

\* -----------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------
Init ==
  /\ towers = [i \in TowerIdx |-> IF i = 1 THEN Total ELSE 0]

\* -----------------------------------------------------------------
\* Move action
\* -----------------------------------------------------------------
Move ==
  \E src \in TowerIdx, dst \in TowerIdx :
    /\ src # dst
    /\ \E d \in DiskVal :
        /\ DiskOn(d, towers[src])               \* d is on source
        /\ d = MinDisk(towers[src])              \* d is smallest on source
        /\ (towers[dst] = 0 \/ d <= MinDisk(towers[dst])) \* no smaller disk on dest
        /\ towers' = [towers EXCEPT ![src] = @ - d,
                                   ![dst] = @ + d]

Next == Move

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_towers

\* -----------------------------------------------------------------
\* Invariants required by the .cfg file
\* -----------------------------------------------------------------
TypeOK ==
  /\ towers \in [TowerIdx -> Nat]
  /\ \A i \in TowerIdx : towers[i] \in 0..Total

Inv ==
  /\ \A i \in TowerIdx : towers[i] = 
       \* recompute the numeric encoding from its set of disks
       SUM { 2^(j-1) : j \in TowerSet(towers[i]) }
  /\ \A i,j \in TowerIdx : i # j => DISJOINT(TowerSet(towers[i]), TowerSet(towers[j]))
  /\ \E i \in TowerIdx : towers[i] = Total

=============================================================================