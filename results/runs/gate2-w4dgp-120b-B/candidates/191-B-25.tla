---- MODULE Hanoi -----------------------------------------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

(****************************************************************************)
(* TRUE iff i is a power of two                                             *)
(****************************************************************************)
PowerOfTwo(i) == i & (i-1) = 0

(****************************************************************************)
(* A set of all powers of two up to n                                       *)
(****************************************************************************)
SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

(****************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in   *)
(* DOMAIN f.                                                                 *)
(****************************************************************************)
Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
          IN  DSum[DOMAIN f]

(****************************************************************************)
(* D is number of disks and N number of towers                               *)
(****************************************************************************)
CONSTANT D, N

(****************************************************************************)
(* Towers of Hanoi with N towers                                             *)
(****************************************************************************)
VARIABLES towers
vars == <<towers>>

(****************************************************************************)
(* The total sum of all towers must amount to the disks in the system       *)
(****************************************************************************)
Inv == Sum(towers) = 2^D - 1

(* Towers are naturals in the interval (0, 2^D] *)
TypeOK == \A i \in DOMAIN towers : towers[i] \in Nat /\ towers[i] < 2^D

(****************************************************************************)
(* Initial predicate: all towers empty except the first, which holds all    *)
(* disks.                                                                    *)
(****************************************************************************)
Init == towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

(****************************************************************************)
(* TRUE iff the tower is empty                                              *)
(****************************************************************************)
IsEmptyTower(tower) == tower = 0

(****************************************************************************)
(* TRUE iff the disk is located on the given tower                          *)
(****************************************************************************)
IsOnTower(tower, disk) == /\ tower # 0
                          /\ (tower & disk) = disk

(****************************************************************************)
(* TRUE iff disk is the top disk on tower                                    *)
(****************************************************************************)
IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
                               /\ (disk - 1) = 0

(****************************************************************************)
(* TRUE iff disk can be moved off of tower                                  *)
(****************************************************************************)
CanMoveOff(tower, disk) == /\ IsOnTower(tower, disk)
                           /\ IsSmallestDisk(tower, disk)

(****************************************************************************)
(* TRUE iff disk can be moved to the tower                                  *)
(****************************************************************************)
CanMoveTo(tower, disk) == \/ tower # 0 /\ (disk - 1) = 0
                          \/ IsEmptyTower(tower)

(****************************************************************************)
(* Move a disk from one tower to another, decreasing the source by the disk  *)
(* and increasing the destination by the disk.                              *)
(****************************************************************************)
Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
                        /\ CanMoveTo(towers[to], disk)
                        /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                                                    ![to] = towers[to] + disk]

(****************************************************************************)
(* Any legal move of any power-of-two-sized disk between two distinct      *)
(* towers.  The "idx2 # idx1" guard cuts the search space in half.           *)
(****************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D): \E idx1, idx2 \in DOMAIN towers:
            /\ idx1 # idx2
            /\ Move(idx1, idx2, d)

Spec == Init /\ [][Next]_vars

(****************************************************************************)
(* The final configuration has all disks on the right tower; TLC checks for *)
(* a counterexample to this "invariant" and prints the move trace when it    *)
(* finds one.  The shortest solution for n disks is 2^n - 1 moves.           *)
(****************************************************************************)
NotSolved == towers[N] # 2^D - 1

=============================================================================