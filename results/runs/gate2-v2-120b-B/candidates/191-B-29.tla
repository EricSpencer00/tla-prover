---- MODULE Hanoi ----
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i # 0 /\ i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n - 1) : PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in *)
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

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                             *)
(***************************************************************************)
TypeOK == /\ \A i \in DOMAIN towers : /\ towers[i] \in Nat
                                 /\ 0 <= towers[i] /\ towers[i] <= 2^D - 1

(***************************************************************************)
(* Initial configuration: all disks on the first tower                      *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the smallest (least significant) disk present on the tower     *)
(***************************************************************************)
SmallestDiskOn(tower) ==
    IF tower = 0 THEN 0
    ELSE CHOOSE d \in SetOfPowerOfTwo(D) : d \in tower

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ disk \in tower
                           /\ disk = SmallestDiskOn(tower)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == /\ (tower = 0) \/ (disk < SmallestDiskOn(tower))

(***************************************************************************)
(* Move a disk from one tower to another                                   *)
(***************************************************************************)
Move(from, to, disk) ==
    /\ CanMoveOff(towers[from], disk)
    /\ CanMoveTo(towers[to], disk)
    /\ towers' = [towers EXCEPT ![from] = towers[from] \ {disk},
                               ![to]   = towers[to]   \cup {disk}]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next ==
    \E d \in SetOfPowerOfTwo(D) :
        \E i, j \in DOMAIN towers :
            /\ i # j
            /\ Move(i, j, d)

(***************************************************************************)
(* Full specification                                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right tower.               *)
(***************************************************************************)
NotSolved == towers[N] # (2^D - 1)

=============================================================================