---- MODULE Hanoi ----
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i # 0 /\ i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == { x \in 1..(2^n - 1) : PowerOfTwo(x) }

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               IF S = {} THEN 0
               ELSE LET elt == CHOOSE e \in S : TRUE
                    IN f[elt] + DSum[S \ {elt}]
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

(* Towers are naturals in the interval [0, 2^D) *)
TypeOK == /\ towers \in [1..N -> Nat]
          /\ \A i \in 1..N : towers[i] < 2^D

(***************************************************************************)
(* Initial predicate: all disks are on the first tower                     *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the disk is contained in the tower (i.e., tower has the disk's *)
(* bits set)                                                               *)
(***************************************************************************)
IsOnTower(tower, disk) == (tower & disk) = disk

(***************************************************************************)
(* TRUE iff disk is the smallest (least‑significant) disk on tower         *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
                               /\ (tower & (disk - 1)) = 0

(***************************************************************************)
(* Disk can be moved off its current tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == IsSmallestDisk(tower, disk)

(***************************************************************************)
(* Disk can be moved to a target tower                                     *)
(***************************************************************************)
CanMoveTo(tower, disk) == \/ IsEmptyTower(tower)
                           \/ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* Move action                                                             *)
(***************************************************************************)
Move(from, to, disk) ==
    /\ CanMoveOff(towers[from], disk)
    /\ CanMoveTo(towers[to], disk)
    /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                               ![to]   = towers[to] + disk]

(***************************************************************************)
(* Next relation: choose a disk (power of two) and two distinct towers,    *)
(* then optionally perform a move.                                          *)
(***************************************************************************)
Next ==
    \E d \in SetOfPowerOfTwo(D) :
        \E from, to \in DOMAIN towers :
            /\ from # to
            /\ (CanMoveOff(towers[from], d) /\ CanMoveTo(towers[to], d) /\ Move(from, to, d)
                \/ UNCHANGED towers)

(***************************************************************************)
(* Full specification                                                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* NotSolved: configuration where final tower does NOT yet contain all disks *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

=============================================================================