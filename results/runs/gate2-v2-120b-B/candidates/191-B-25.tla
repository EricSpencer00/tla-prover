---- MODULE Hanoi ----
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i - 1) = 0

(***************************************************************************)
(* A set of all powers of two up to n                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == { x \in 1..(2 ^ n - 1) : PowerOfTwo(x) }

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
Inv == Sum(towers) = 2 ^ D - 1

(* Towers are naturals in the interval [0, 2^D) *)
TypeOK == /\ \A i \in DOMAIN towers : towers[i] \in Nat /\ towers[i] < 2 ^ D

(***************************************************************************)
(* Initial predicate                                                       *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the smallest disk on a tower is represented by its value       *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ tower >= disk
                               /\ disk \in SetOfPowerOfTwo(D)
                               /\ (tower + disk) \in SetOfPowerOfTwo(D)

(***************************************************************************)
(* TRUE iff a disk can be moved off a given tower                           *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ IsSmallestDisk(tower, disk)
                           /\ tower >= disk

(***************************************************************************)
(* TRUE iff a disk can be moved onto a given tower                         *)
(***************************************************************************)
CanMoveTo(tower, disk) == \/ IsEmptyTower(tower)
                           \/ IsSmallestDisk(tower, disk)
(***************************************************************************)
(* Move action                                                            *)
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
        \E idx1, idx2 \in DOMAIN towers :
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

(***************************************************************************)
(* Full specification                                                     *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

=============================================================================