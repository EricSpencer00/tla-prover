---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT D
CONSTANT N

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
DiskSet == 0 .. (2^D - 1) \ {0}          \* all non‑zero values that fit D bits
Towers   == 1 .. N                       \* tower indices

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLE towers   \* a function [Towers -> Nat] giving the bit‑mask of each tower

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
FullMask == 2^D - 1

(* Disk? returns TRUE iff d is a power of two and fits in D bits *)
Disk?(d) == d \in DiskSet /\ \A k \in 1..(D-1) : (2^k) \in DiskSet => (d # 2^k)

(* SmallestDisk(t) returns the smallest disk present on tower t,
   or 0 if the tower is empty. *)
SmallestDisk(t) == 
  IF towers[t] = 0 THEN 0
  ELSE
    LET bits == { k \in 0..(D-1) : ((towers[t] DIV 2^k) % 2) = 1 } IN
      2 ^ (Min(bits))

(* DiskOnTower(d, t) holds iff disk d is present on tower t *)
DiskOnTower(d, t) == ((towers[t] DIV d) % 2) = 1

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init == 
  /\ towers = [i \in Towers |-> IF i = 1 THEN FullMask ELSE 0]

(*-----------------------------------------------------------------
  Move action
-----------------------------------------------------------------*)
Move ==
  \E d \in DiskSet, s \in Towers, dst \in Towers :
    /\ s # dst
    /\ DiskOnTower(d, s)                           \* d is on source
    /\ d = SmallestDisk(s)                         \* d is the topmost on source
    /\ (towers[dst] = 0 \/ d < SmallestDisk(dst)) \* cannot place on smaller
    /\ towers' = [towers EXCEPT 
          ![s] = towers[s] - d,
          ![dst] = towers[dst] + d]

Next == Move

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
TypeOK == 
  /\ towers \in [Towers -> Nat]
  /\ \A i \in Towers : towers[i] \in 0..FullMask

Inv == 
  /\ towers \in [Towers -> Nat]
  /\ \A i \in Towers : towers[i] \in 0..FullMask
  /\ \A i \in Towers : \A k \in DiskSet :
        DiskOnTower(k, i) => Disk?(k)               \* only valid disks appear
  /\ \A i \in Towers : 
        \A d1, d2 \in DiskSet :
          (DiskOnTower(d1, i) /\ DiskOnTower(d2, i) /\ d1 < d2) => 
            \E smaller \in DiskSet : (smaller < d1) /\ DiskOnTower(smaller, i) = FALSE
  /\ \A i \in Towers : towers[i] = \Sum_{k \in DiskSet} 
        IF DiskOnTower(k, i) THEN k ELSE 0
  /\ \Sum_{i \in Towers} towers[i] = FullMask

=============================================================================