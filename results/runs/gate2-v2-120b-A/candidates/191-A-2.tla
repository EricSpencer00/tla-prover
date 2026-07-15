---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(* Constants *)
CONSTANT D \* number of disks (must be >= 1)
CONSTANT N \* number of towers (must be >= 3 for the classic puzzle)

(***************************************************************************)
(* Derived constants *)
DiskValues == { 2^i : i \in 0..(D-1) }           \* the set of all disk values, each a power of two
Disks      == 1..D                               \* abstract indices for the D disks
Towers     == 1..N                               \* tower identifiers

(***************************************************************************)
(* State variable: an array (function) mapping each tower to the sum of the
   disk values currently on that tower. The sum encodes the set of disks via
   its binary representation. *)
VARIABLES TowerVals

(***************************************************************************)
(* Helper definitions *)
(* Bitwise AND expressed arithmetically: the result is the sum of the powers
   of two that appear in both arguments. *)
BitAnd(a, b) == 
  LET bits == { i \in 0..(D-1) : (a % 2^(i+1) >= 2^i) /\ (b % 2^(i+1) >= 2^i) } 
  IN  IF bits = {} THEN 0 ELSE \Sum i \in bits : 2^i

(* Returns the smallest (least significant) set bit of a non‑zero natural number,
   i.e., the value of the smallest disk present. *)
SmallestDisk(v) == 
  IF v = 0 THEN 0 
  ELSE 2 ^ ( 
        CHOOSE i \in 0..(D-1) : 
          (v % 2^(i+1) >= 2^i) 
      )

(* Checks that a candidate disk is indeed a power of two and within the allowed range. *)
IsDisk(d) == d \in DiskValues

(***************************************************************************)
(* Initialization: all disks are on tower 1, all other towers are empty. *)
Init ==
  /\ TowerVals = [t \in Towers |-> IF t = 1 THEN 2^D - 1 ELSE 0]
  /\ TypeOK

(***************************************************************************)
(* Type correctness invariant (used also as a safety invariant). *)
TypeOK ==
  /\ TowerVals \in [Towers -> Nat]
  /\ \A t \in Towers : TowerVals[t] \in 0..(2^D - 1)

(***************************************************************************)
(* Safety invariant required by the .cfg file. *)
Inv == 
  /\ TypeOK
  /\ \A t \in Towers : TowerVals[t] \in 0..(2^D - 1)
  /\ \Sum t \in Towers : TowerVals[t] = 2^D - 1

(***************************************************************************)
(* Move action: nondeterministically choose a source tower, a destination tower,
   and a disk to move, subject to the Hanoi constraints. *)
Move == 
  \E src \in Towers, dst \in Towers :
    /\ src # dst
    /\ \E d \in DiskValues :
        /\ (TowerVals[src] % (2 * d) >= d)          \* d is present on src
        /\ SmallestDisk(TowerVals[src]) = d        \* d is the smallest disk on src
        /\ (TowerVals[dst] % (2 * d) < d)          \* no smaller disk on dst
        /\ TowerVals' = [TowerVals EXCEPT 
                ![src] = TowerVals[src] - d,
                ![dst] = TowerVals[dst] + d]

(***************************************************************************)
(* Stuttering step to avoid deadlock when the puzzle is solved. *)
Stutter == UNCHANGED TowerVals

(***************************************************************************)
(* Next-state relation. *)
Next == Move \/ Stutter

(***************************************************************************)
(* Specification required by the .cfg file. *)
Spec == Init /\ [][Next]_<<TowerVals>>

(***************************************************************************)
(* Theorem (optional, for readers) that Spec implies the safety invariant. *)
THEOREM SpecImpliesInv == Spec => []Inv

====