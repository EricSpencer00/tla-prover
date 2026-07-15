---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------*)
(* Constants representing the number of disks (D) and towers (N).      *)
(*--------------------------------------------------------------------)
CONSTANT D
CONSTANT N

(*--------------------------------------------------------------------*)
(* Derived constant: the maximal value representing all disks.        *)
(*--------------------------------------------------------------------)
MaxVal == 2 ^ D - 1

(*--------------------------------------------------------------------*)
(* DiskSet: the set of all disks, each represented by a power of two. *)
(*--------------------------------------------------------------------)
DiskSet == { 2 ^ i : i \in 0 .. (D - 1) }

(*--------------------------------------------------------------------*)
(* Tower indices.                                                     *)
(*--------------------------------------------------------------------)
Idx == 1 .. N

(*--------------------------------------------------------------------*)
(* State variable: each tower holds a natural number encoding the     *)
(* disks present on that tower (bits).                                 *)
(*--------------------------------------------------------------------)
VARIABLES towers

(*--------------------------------------------------------------------*)
(* Helper definitions.                                                *)
(*--------------------------------------------------------------------)

(* The smallest disk present on a tower t, or 0 if the tower is empty. *)
SmallestDisk(t) == 
    IF towers[t] = 0 
    THEN 0 
    ELSE CHOOSE d \in DiskSet : (towers[t] /\ d) = d

(* The sum of all tower values.                                      *)
SumTowers == \Sum_{i \in Idx} towers[i]

(* Type correctness predicate for a single tower value.               *)
TowerTypeOK(v) == v \in Nat /\ v >= 0 /\ v <= MaxVal

(*--------------------------------------------------------------------*)
(* Initial state: all disks are on the first tower.                   *)
(*--------------------------------------------------------------------)
Init ==
    /\ towers = [i \in Idx |-> IF i = 1 THEN MaxVal ELSE 0]
    /\ \A i \in Idx : TowerTypeOK(towers[i])

(*--------------------------------------------------------------------*)
(* A legal move selects a source tower, a destination tower, and a    *)
(* disk (a power of two). The move is allowed only if the disk is the *)
(* smallest on the source tower and no smaller disk is on the         *)
(* destination tower.                                                  *)
(*--------------------------------------------------------------------)
Move ==
    \E src \in Idx, dst \in Idx, d \in DiskSet :
        /\ src # dst
        /\ towers[src] >= d                     \* disk is present in src
        /\ SmallestDisk(src) = d                \* it is the smallest on src
        /\ (towers[dst] = 0 \/ SmallestDisk(dst) > d)   \* dst has no smaller disk
        /\ towers' = [towers EXCEPT 
                        ![src] = towers[src] - d,
                        ![dst] = towers[dst] + d]

(*--------------------------------------------------------------------*)
(* Next-state relation: either a legal move occurs or the system stays*)
(* in the same state (stuttering).                                    *)
(*--------------------------------------------------------------------)
Next == Move \/ UNCHANGED towers

(*--------------------------------------------------------------------*)
(* Specification variable for the model checker.                       *)
(*--------------------------------------------------------------------)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------*)
(* Invariant: conservation of total disk value.                        *)
(*--------------------------------------------------------------------)
Inv == SumTowers = MaxVal

(*--------------------------------------------------------------------*)
(* Type correctness invariant.                                        *)
(*--------------------------------------------------------------------)
TypeOK == \A i \in Idx : TowerTypeOK(towers[i])

====