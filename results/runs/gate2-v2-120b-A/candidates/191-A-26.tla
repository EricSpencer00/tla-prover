---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS D, N

(* ------------------------------------------------------------------- *)
(* Derived constants *)
DiskSet == 1 .. D
TowerSet == 1 .. N

(* Disk size as power of two: disk k has size 2^(k-1) *)
DiskSize(k) == 2 ^ (k - 1)

(* The total sum of all disk sizes, used for conservation *)
Total == 2 ^ D - 1

(* ------------------------------------------------------------------- *)
(* State variable: an array (function) mapping each tower to the sum of
   the sizes of the disks currently on that tower. The sum of all entries
   must always equal Total. *)
VARIABLE towers

(* ------------------------------------------------------------------- *)
(* Helper predicates *)

(* Returns the set of disks present on a given tower, derived from the
   bitwise encoding. *)
DisksOn(t) == { k \in DiskSet : (towers[t] /\  DiskSize(k)) # 0 }

(* The smallest (i.e., topmost) disk on a tower, or 0 if the tower is empty. *)
SmallestDisk(t) ==
  IF towers[t] = 0 THEN 0
  ELSE CHOOSE k \in DiskSet : DiskSize(k) <= towers[t] /\ (towers[t] /\ DiskSize(k)) # 0
                         /\ \A j \in DiskSet :
                               j < k => (towers[t] /\ DiskSize(j)) = 0

(* Predicate that checks whether a move of a given disk from source to dest
   satisfies the Tower of Hanoi rules. *)
ValidMove(disk, src, dest) ==
  /\ src \in TowerSet /\ dest \in TowerSet /\ src # dest
  /\ disk \in DiskSet
  /\ towers[src] /\ DiskSize(disk) # 0               \* disk is present on src
  /\ DiskSize(disk) = SmallestDisk(src)              \* it is the topmost disk on src
  /\ (towers[dest] = 0 \/ DiskSize(disk) < SmallestDisk(dest))

(* ------------------------------------------------------------------- *)
(* Initial state: all disks on the first tower *)
Init ==
  /\ towers = [t \in TowerSet |-> IF t = 1 THEN Total ELSE 0]

(* ------------------------------------------------------------------- *)
(* Next-state relation: nondeterministically choose a legal move *)
Move ==
  \E disk \in DiskSet :
    \E src, dest \in TowerSet :
      /\ src # dest
      /\ ValidMove(disk, src, dest)
      /\ towers' = [t \in TowerSet |-> 
                     IF t = src THEN towers[t] - DiskSize(disk)
                     ELSE IF t = dest THEN towers[t] + DiskSize(disk)
                     ELSE towers[t]]

Next == Move

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<towers>>

(* ------------------------------------------------------------------- *)
(* Type correctness invariant: each tower value is a natural number
   less than 2^D, and the sum of all tower values equals Total *)
TypeOK ==
  /\ \A t \in TowerSet : towers[t] \in Nat
  /\ \A t \in TowerSet : towers[t] < 2 ^ D
  /\ \A t \in TowerSet : towers[t] >= 0
  /\ \A t \in TowerSet : towers[t] <= Total
  /\ \A t \in TowerSet : 
        \A d \in DiskSet :
          (towers[t] /\ DiskSize(d)) # 0 => d \in DiskSet
  /\ \A t \in TowerSet :
        \A d1, d2 \in DiskSet :
          (towers[t] /\ DiskSize(d1)) # 0 /\ (towers[t] /\ DiskSize(d2)) # 0 =>
            (d1 = d2) \/ (DiskSize(d1) # DiskSize(d2))
  /\ \Sum t \in TowerSet : towers[t] = Total

(* ------------------------------------------------------------------- *)
(* Safety invariant: conservation of the total sum of disk sizes *)
Inv == \Sum t \in TowerSet : towers[t] = Total

=================================