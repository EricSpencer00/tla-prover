------------------------------- MODULE Hanoi -------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i-1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
          IN  DSum[DOMAIN f]

(***************************************************************************)
(* D is number of disks and N number of towers                             *)
(***************************************************************************)
CONSTANT D, N

(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Inv == Sum(towers) = 2^D - 1

(***************************************************************************)
(* Towers are natural numbers in the interval [0, 2^D)                       *)
(***************************************************************************)
TypeOK == /\ \A i \in DOMAIN towers : towers[i] \in Nat
          /\ \A i \in DOMAIN towers : towers[i] < 2^D

(***************************************************************************)
(* Initial predicate: all disks on the first tower, the others empty       *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(t) == t = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)
IsOnTower(tower, disk) == /\ disk \in SetOfPowerOfTwo(D)
                           /\ tower >= disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower (i.e., the least significant *)
(*  power‑of‑two present in the tower)                                      *)
(***************************************************************************)
IsSmallestDisk(tower, disk) ==
    /\ IsOnTower(tower, disk)
    /\ (tower \ disk) < disk

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == IsEmptyTower(tower) \/ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* Action that moves a disk from one tower to another                     *)
(***************************************************************************)
Move(from, to, disk) ==
    /\ CanMoveOff(towers[from], disk)
    /\ CanMoveTo(towers[to], disk)
    /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                            ![to]   = towers[to]   + disk]

(***************************************************************************)
(* All possible moves                                                     *)
(***************************************************************************)
Next ==
    \E d \in SetOfPowerOfTwo(D) :
        \E idx1, idx2 \in DOMAIN towers :
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

(***************************************************************************)
(* Specification: Init and stuttering closure of Next                     *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the rightmost tower           *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

=============================================================================