---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT D \* number of disks (must be >= 1)
CONSTANT N \* number of towers (must be >= 2)

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
DiskSet == 1 .. D
TowerSet == 1 .. N

(* Disk value is 2^(k-1) for disk k *)
DiskValue(k) == 2^(k - 1)

AllDisks == UNION { DiskValue(k) : k \in DiskSet }

(* Full set of bits for all disks: 2^D - 1 *)
FullMask == 2^D - 1

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES towers

(*-----------------------------------------------------------------
  Type definitions
-----------------------------------------------------------------*)
TowerValues == 0 .. FullMask

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ towers = [i \in TowerSet |-> IF i = 1 THEN FullMask ELSE 0]
    /\ /\ towers[1] \in TowerValues
       /\ \A i \in TowerSet \ {1} : towers[i] \in TowerValues

(*-----------------------------------------------------------------
  Helper predicates
-----------------------------------------------------------------*)
(* A number v is a power of two iff it is >0 and has exactly one 1 bit *)
IsPowerOfTwo(v) == v > 0 /\ v /\ (v - 1) = 0

(* The smallest disk present on tower t (0 if tower empty) *)
SmallestDisk(t) ==
    IF towers[t] = 0 THEN 0
    ELSE 2 ^ ( (Cardinality({ k \in DiskSet : DiskValue(k) \in towers[t] })) - 1)  
         \* Not used directly; provided for readability.

(* The set of disk values currently on tower t *)
DiskSetOn(t) == { DiskValue(k) : k \in DiskSet /\ (DiskValue(k) \in towers[t]) }

(* The smallest disk value on a non‑empty tower t *)
TopDisk(t) ==
    IF towers[t] = 0 THEN 0
    ELSE
        CHOOSE d \in DiskSetOn(t) :
            \A e \in DiskSetOn(t) : e >= d

(*-----------------------------------------------------------------
  Move action
-----------------------------------------------------------------*)
Move ==
    \E src \in TowerSet, dst \in TowerSet, d \in DiskSet :
        /\ src # dst
        /\ d \in DiskSetOn(src)                 \* the disk is on the source
        /\ d = TopDisk(src)                      \* it is the smallest on src
        /\ ( towers[dst] = 0 \/ d < TopDisk(dst) ) \* no smaller disk on dst
        /\ towers' = [t \in TowerSet |-> 
                        IF t = src THEN towers[t] - d
                        ELSE IF t = dst THEN towers[t] + d
                        ELSE towers[t]]

Next == Move

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
(* Type correctness *)
TypeOK == 
    /\ towers \in [TowerSet -> TowerValues]
    /\ \A i \in TowerSet : towers[i] \in TowerValues

(* Conservation of all disks *)
Inv == 
    /\ \A i \in TowerSet : towers[i] \in TowerValues
    /\ \A i \in TowerSet : towers[i] = 0 \/ IsPowerOfTwo(towers[i]) \/ 
           (\E s \in Subset(AllDisks) : towers[i] = +/ s)
    /\ \A i \in TowerSet :
        \A d \in DiskSetOn(i) : d \in AllDisks
    /\ \A i, j \in TowerSet : i # j => DiskSetOn(i) \cap DiskSetOn(j) = {}

    /\ \Sum_{i \in TowerSet} towers[i] = FullMask

(*-----------------------------------------------------------------
  TLAPS and model-checker entry points
-----------------------------------------------------------------*)
\* The reference .cfg expects the following identifiers
Spec == Spec
TypeOK == TypeOK
Inv == Inv

====