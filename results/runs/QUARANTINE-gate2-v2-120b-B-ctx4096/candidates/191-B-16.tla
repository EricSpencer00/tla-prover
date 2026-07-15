---- MODULE Hanoi ----
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i # 0 /\ i = 2 ^ (i - 1)

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n - 1) : PowerOfTwo(x)}

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
(* Towers are naturals in the interval [0, 2^D)                             *)
(***************************************************************************)
TypeOK == /\ \A i \in DOMAIN towers :
               /\ towers[i] \in Nat
               /\ towers[i] >= 0
               /\ towers[i] < 2^D

(***************************************************************************)
(* Initial state: all disks on the first tower.                             *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                              *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff disk is the smallest (i.e., least significant set) on tower   *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ (tower \% (2 * disk)) = 0
                               /\ (disk \in SetOfPowerOfTwo(D))

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                   *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved onto tower                                    *)
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
                               ![to]   = towers[to]   + disk]

(***************************************************************************)
(* Next relation: nondeterministically choose a disk (power of two) and      *)
(* two distinct towers, then either stay (stutter) or perform the move.    *)
(***************************************************************************)
Next ==
    \/ \E d \in SetOfPowerOfTwo(D) :
          \E i, j \in DOMAIN towers :
              i # j /\ Move(i, j, d)
    \/ UNCHANGED towers

(***************************************************************************)
(* Full specification                                                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* NotSolved: the final tower (tower N) does not yet contain all disks      *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

=============================================================================