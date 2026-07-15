------------------------------- MODULE Hanoi -------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to D                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == { x \in 1..(2^n - 1) : PowerOfTwo(x) }

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN IF S = {} THEN 0
                     ELSE f[elt] + DSum[S \ {elt}]
          IN DSum[DOMAIN f]

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
CONSTANT D, N

(***************************************************************************)
(* Variables representing each tower as a natural number encoding the set   *)
(* of disks it currently holds. The encoding uses a bitmask: the i‑th bit *)
(* (counting from 0) is 1 iff the disk of size 2^i is present on that tower*)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Inv == Sum(towers) = 2^D - 1

(***************************************************************************)
(* Towers are natural numbers that encode a subset of {1,2,…,2^D-1} using   *)
(* a bitmask. Therefore each tower value must be strictly less than 2^D.   *)
(***************************************************************************)
TypeOK == /\ \A i \in DOMAIN towers : towers[i] \in Nat
          /\ \A i \in DOMAIN towers : towers[i] < 2^D

(***************************************************************************)
(* Initial state: all disks are on the first tower, all others are empty.  *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the disk (represented by a power of two) is located on the     *)
(* given tower.                                                            *)
(***************************************************************************)
IsOnTower(tower, disk) == tower & disk = disk

(***************************************************************************)
(* TRUE iff disk is the smallest (least‑significant) disk on tower.        *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
                               /\ tower & (disk - 1) = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ IsOnTower(tower, disk)
                           /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == \/ tower & (disk - 1) = 0
                          \/ IsEmptyTower(tower)

(***************************************************************************)
(* Action that moves a single disk from one tower to another.              *)
(***************************************************************************)
Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
                        /\ CanMoveTo(towers[to], disk)
                        /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                                                ![to]   = towers[to]   + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D) :
          \E idx1, idx2 \in DOMAIN towers :
             /\ idx1 # idx2
             /\ Move(idx1, idx2, d)

(***************************************************************************)
(* Full specification: init followed by steps that satisfy Next.           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right (N‑th) tower.        *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

=============================================================================