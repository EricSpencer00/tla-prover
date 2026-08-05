---- MODULE Hanoi ------------------------------------------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(***************************************************************************)
(* TRUE iff i is a power of two.                                            *)
(***************************************************************************)
PowerOfTwo(i) == i & (i-1) = 0

(***************************************************************************)
(* A set of all powers of two up to n.                                      *)
(***************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in the*)
(* domain of f.                                                             *)
(***************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
              LET elt == CHOOSE e \in S : TRUE
              IN  IF S = {} THEN 0
                        ELSE f[elt] + DSum[S \ {elt}]
          IN  DSum[DOMAIN f]

(***************************************************************************)
(* D is number of disks and N number of towers.                             *)
(***************************************************************************)
CONSTANT D, N

(***************************************************************************)
(* Towers of Hanoi with N towers.                                            *)
(***************************************************************************)
VARIABLES towers
vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system.      *)
(***************************************************************************)
Inv == Sum(towers) = 2^D - 1

(* Towers are naturals in the interval (0, 2^D]                          *)
TypeOK == \A i \in DOMAIN towers : towers[i] \in 0..(2^D-1)

(***************************************************************************)
(* Initial condition: all towers empty except the first, holding all disks. *)
(***************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty.                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower.                             *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ tower # 0
                               /\ disk <= tower
                               /\ (disk & (disk-1)) = 0
                               /\ (tower & (disk-1)) = 0

(***************************************************************************)
(* TRUE iff disk can be moved off tower.                                    *)
(***************************************************************************)
CanMoveOff(tower, disk) == tower # 0 /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved onto the tower.                               *)
(***************************************************************************)
CanMoveTo(tower, disk) == \/ tower = 0
                          \/ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* Move disk from one tower to another.                                     *)
(***************************************************************************)
Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
                        /\ CanMoveTo(towers[to], disk)
                        /\ towers' = [towers EXCEPT ![from] = @ - disk, ![to] = @ + disk]

(***************************************************************************)
(* Next-step relation: a legal move of a power-of-two disk between two      *)
(* distinct towers.                                                         *)
(***************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D): \E idx1, idx2 \in DOMAIN towers:
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

(***************************************************************************)
(* The complete system specification.                                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

=============================================================================