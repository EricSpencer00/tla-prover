---- MODULE Hanoi ----------------------------------------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two.                                            *)
(* Repurposed to mean a power of two that is less than 2^D, the total       *)
(* number of disks, added a range check to avoid out-of-bounds arithmetic *)
(* when forestalling the tower overflow.                                    *)
(***************************************************************************)
PowerOfTwo(i) == i & (i - 1) = 0 /\ i < 2 ^ D

(***************************************************************************)
(* A set of all powers of two up to but not including D disks.              *)
(***************************************************************************)
SetOfPowerOfTwo(d) == {x \in 1..(2 ^ d - 1): PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library: the sum of f[x] for all x in    *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN IF S = {} THEN 0 ELSE f[elt] + DSum[S \ {elt}]
          IN DSum[DOMAIN f]

CONSTANT D, N

(***************************************************************************)
(* Towers of Hanoi with N towers. Towers are represented as natural numbers  *)
(* encoding which disks sit on them as a sum of powers of two.              *)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must equal the disks in the system:          *)
(* 2^D - 1 is the sum of the first D powers of two.                         *)
(***************************************************************************)
Inv == Sum(towers) = 2 ^ D - 1

(***************************************************************************)
(* Towers are natural numbers in 0..(2^D-1).                                  *)
(***************************************************************************)
TypeOK == \A i \in DOMAIN towers : towers[i] \in Nat /\ towers[i] < 2 ^ D

(***************************************************************************)
(* Initially all disks sit on the first tower.                               *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty.                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff disk is on the given tower.                                     *)
(***************************************************************************)
IsOnTower(tower, disk) == tower & disk = disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on the tower.                         *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == IsOnTower(tower, disk) /\ disk - 1 = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower: it's on the tower and is       *)
(* the smallest disk there.                                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == IsOnTower(tower, disk) /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be placed on the tower: the tower is empty or disk is  *)
(* smaller than any disk already on it.                                     *)
(***************************************************************************)
CanMoveTo(tower, disk) == tower & (disk - 1) = 0 \/ IsEmptyTower(tower)

(***************************************************************************)
(* Moving a disk from one tower to another.                                  *)
(***************************************************************************)
Move(from, to, disk) ==
    /\ CanMoveOff(towers[from], disk)
    /\ CanMoveTo(towers[to], disk)
    /\ towers' = [towers EXCEPT ![from] = towers[from] - disk, ![to] = towers[to] + disk]

(***************************************************************************)
(* Every possible move: any disk that is a power of two below 2^D from any  *)
(* source tower to any distinct destination tower.                          *)
(***************************************************************************)
Next ==
    \E d \in SetOfPowerOfTwo(D) :
        \E idx1, idx2 \in DOMAIN towers :
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

(***************************************************************************)
(* The system starts in Init and every step follows Next.                   *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The puzzle is solved when all disks sit on the last tower.               *)
(***************************************************************************)
NotSolved == towers[N] # 2 ^ D - 1

=============================================================================