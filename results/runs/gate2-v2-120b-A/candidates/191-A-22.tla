---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT D
CONSTANT N

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
DiskValues == { 2 ^ i : i \in 0..(D-1) }

AllDisksMask == 2 ^ D - 1

Towers == 1..N

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES towers

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
(* Convert a tower value to the set of disks (powers of two) it contains *)
TowerSet(t) == { d \in DiskValues : d \in towers[t] }

(* Minimum (smallest) disk present on a tower, or 0 if the tower is empty *)
MinDisk(t) ==
  IF towers[t] = 0 THEN 0
  ELSE
    CHOOSE d \in DiskValues :
      /\ d \in TowerSet(t)
      /\ \A e \in TowerSet(t) : d <= e

(*-----------------------------------------------------------------
  Type correctness predicate (used as an invariant)
-----------------------------------------------------------------*)
TypeOK ==
  /\ towers \in [Towers -> Nat]
  /\ \A t \in Towers : towers[t] \in 0..AllDisksMask

(*-----------------------------------------------------------------
  Conservation invariant (used as an invariant)
-----------------------------------------------------------------*)
Inv ==
  /\ \A t \in Towers : towers[t] \in 0..AllDisksMask
  /\ \Sum_{t \in Towers} towers[t] = AllDisksMask

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ towers = [t \in Towers |-> IF t = 1 THEN AllDisksMask ELSE 0]
  /\ TypeOK

(*-----------------------------------------------------------------
  Action: move a disk from a source tower to a destination tower
-----------------------------------------------------------------*)
Move ==
  \E d \in DiskValues :
    \E src \in Towers :
      \E dst \in Towers :
        /\ src # dst
        /\ (towers[src] /\ d) = d                      \* disk present on source
        /\ (towers[src] /\ (d - 1)) = 0                \* d is smallest on source
        /\ (towers[dst] /\ (d - 1)) = 0                \* no smaller disk on dest
        /\ towers' = [t \in Towers |-> 
                        IF t = src THEN towers[t] - d
                        ELSE IF t = dst THEN towers[t] + d
                        ELSE towers[t]]
        /\ TypeOK

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ Move
  \/ UNCHANGED towers

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

=============================================================================