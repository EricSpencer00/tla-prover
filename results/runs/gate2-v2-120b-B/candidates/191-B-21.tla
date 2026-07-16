---- MODULE Hanoi ----
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n - 1) : PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) ==
  LET DSum[S \in SUBSET DOMAIN f] ==
    LET elt == CHOOSE e \in S : TRUE
    IN IF S = {} THEN 0 ELSE f[elt] + DSum[S \ {elt}]
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

(* Towers are naturals in the interval [0, 2^D-1] *)
TypeOK == /\ \A i \in DOMAIN towers : towers[i] \in Nat /\ towers[i] <= 2^D - 1

(***************************************************************************)
(* Initial predicate: all disks are on tower 1                             *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower (bit‑wise test)         *)
(***************************************************************************)
IsOnTower(tower, disk) == (tower & disk) = disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower (no smaller bits set)      *)
(***************************************************************************)
IsSmallestDisk(tower, disk) ==
  /\ IsOnTower(tower, disk)
  /\ (tower & (disk - 1)) = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) ==
  /\ IsOnTower(tower, disk)
  /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) ==
  \/ (tower & (disk - 1)) = 0
  \/ IsEmptyTower(tower)

(***************************************************************************)
(* Perform a move of a single disk from one tower to another               *)
(***************************************************************************)
Move(from, to, disk) ==
  /\ CanMoveOff(towers[from], disk)
  /\ CanMoveTo(towers[to], disk)
  /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                             ![to]   = towers[to] + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next ==
  \E d \in SetOfPowerOfTwo(D) :
    \E i, j \in DOMAIN towers :
      i # j /\ Move(i, j, d)

(***************************************************************************)
(* Full specification: Init and stuttering-enabled Next                    *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

=============================================================================