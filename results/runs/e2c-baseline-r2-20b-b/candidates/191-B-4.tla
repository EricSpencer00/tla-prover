---- MODULE Hanoi
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

(* Towers are naturals in the interval (0, 2^D] *)
TypeOK == /\ \A i \in DOMAIN towers : /\ towers[i] \in Nat
                                      /\ towers[i] < 2^D
          
(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0] 

(***************************************************************************)
(* TRUE iff the tower is empty                                             *)
(***************************************************************************)
IsEmptyTower(tower) == tower = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                         *)
(***************************************************************************)    
IsOnTower(tower, disk) == /\ tower & disk = disk

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                             *)
(***************************************************************************)
IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
                               /\ tower & (disk - 1) = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                 *)
(***************************************************************************)
CanMoveOff(tower, disk) == /\ IsOnTower(tower, disk)
                           /\ IsSmallestDisk(tower, disk)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                 *)
(***************************************************************************)
CanMoveTo(tower, disk) == 
    IsEmptyTower(tower) \/
    /\ tower & disk = 0
    /\ tower & (disk - 1) = 0

(***************************************************************************)
(* Move action                                                            *)
(***************************************************************************)
Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
                        /\ CanMoveTo(towers[to], disk)
                        /\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
                                                    ![to] = towers[to] + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next == \E d \in SetOfPowerOfTwo(D): \E idx1, idx2 \in DOMAIN towers: 
            /\ idx1 # idx2 \/ Move(idx1, idx2, d)
    
(***************************************************************************)
(* Spec                                                                *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated. If violation can be *)
(* found, the stack trace shows the steps to solve the Hanoi problem.      *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,    *)
(* which will cause it to print out an "error trace" consisting of a       *)
(* behavior ending in a state where NotSolved is false. With three disks,  *)
(* and three towers the puzzle can be solved in seven moves.               *)
(* The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
(* generally is 2n - 1, where n is the number of disks. Thus, the counter- *)
(* examples shown by TLC will be of length 2n-1                            *)
(***************************************************************************)
=============================================================================