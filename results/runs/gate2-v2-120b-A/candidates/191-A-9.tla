---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
DiskVals == { 2 ^ i : i \in 0..(D-1) }

Disks == DiskVals

Towers == 1..N

AllOnFirst == 2 ^ D - 1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES towerVals

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* Bitwise AND expressed arithmetically *)
BitAnd(m, n) == 
  IF n = 0 THEN 0
  ELSE IF n % 2 = 1 THEN 
          IF m % 2 = 1 THEN 1 + 2 * BitAnd(m \div 2, n \div 2)
          ELSE 2 * BitAnd(m \div 2, n \div 2)
       ELSE 2 * BitAnd(m \div 2, n \div 2)

IsPowerOfTwo(x) == 
  /\ x \in Nat
  /\ x # 0
  /\ \E k \in 0..(D-1) : x = 2 ^ k

(* Disk is present on tower t *)
DiskOnTower(d, t) == (BitAnd(towerVals[t], d) = d)

(* Return the smallest disk on a tower, or 0 if the tower is empty *)
SmallestDisk(t) ==
  IF towerVals[t] = 0 THEN 0
  ELSE 
    CHOOSE d \in DiskVals : DiskOnTower(d, t) /\ 
        \A d2 \in DiskVals : (d2 < d) => ~DiskOnTower(d2, t)

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
  /\ towerVals \in [Towers -> Nat]
  /\ towerVals[1] = AllOnFirst
  /\ \A i \in 2..N : towerVals[i] = 0
  /\ \A i \in Towers : towerVals[i] < 2 ^ D

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)
Move ==
  \E src \in Towers, dst \in Towers, d \in DiskVals :
    /\ src # dst
    /\ DiskOnTower(d, src)
    /\ SmallestDisk(src) = d
    /\ (towerVals[dst] = 0 \/ SmallestDisk(dst) > d)
    /\ towerVals' = [towerVals EXCEPT 
          ![src] = towerVals[src] - d,
          ![dst] = towerVals[dst] + d]

Next == Move

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towerVals>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
(* Type correctness: each tower value is a natural number less than 2^D *)
TypeOK == 
  /\ towerVals \in [Towers -> Nat]
  /\ \A i \in Towers : towerVals[i] < 2 ^ D

(* Conservation of disks: sum of all tower values equals AllOnFirst *)
Inv == 
  /\ \A i \in Towers : towerVals[i] \in Nat
  /\ \A i \in Towers : towerVals[i] < 2 ^ D
  /\ \A i \in Towers : 0 <= towerVals[i]
  /\ Sum(towerVals) = AllOnFirst

=============================================================================