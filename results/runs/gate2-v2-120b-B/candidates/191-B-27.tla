------------------------------- MODULE Hanoi -------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i # 0 /\ i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to D                                      *)
(***************************************************************************)
SetOfPowerOfTwo(D) == {x \in 1..(2^D - 1): PowerOfTwo(x)}

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
(* Towers of Hanoi with N towers                                           *)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system      *)
(***************************************************************************)
Inv == Sum(towers) = 2^D - 1

(***************************************************************************)
(* Towers are naturals in the interval [0, 2^D)                              *)
(***************************************************************************)
TypeOK == /\ \A i \in DOMAIN towers : towers[i] \in Nat
          /\ \A i \in DOMAIN towers : towers[i] >= 0
          /\ \A i \in DOMAIN towers : towers[i] < 2^D

(***************************************************************************)
(* Initial predicate: all disks are on the first tower                     *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff disk is the smallest (least‑significant) disk on the tower     *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == 
    /\ tower >= disk
    /\ (tower - disk) % (2 * disk) = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of a tower                               *)
(***************************************************************************)
CanMoveOff(tower, disk) == IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved onto a tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == 
    \/ IsEmptyTower(tower)
    \/ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* Perform the move, preserving the sum invariant                           *)
(***************************************************************************)
Move(from, to, disk) == 
    /\ CanMoveOff(towers[from], disk)
    /\ CanMoveTo(towers[to], disk)
    /\ towers' = [towers EXCEPT 
                    ![from] = towers[from] - disk,
                    ![to]   = towers[to]   + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D):
          \E idx1, idx2 \in DOMAIN towers:
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

(***************************************************************************)
(* Full specification                                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

=============================================================================