---- MODULE Hanoi ----
EXTENDS Naturals, TLC

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANT D \* number of disks, must be >= 1
CONSTANT N \* number of towers, must be >= 2

(***************************************************************************)
(* Derived constants                                                       *)
(***************************************************************************)
DiskSet == 1 .. D

Disk(k) == 2 ^ (k - 1)          \* size of disk k, a power of two
ALL_DISKS == { Disk(k) : k \in DiskSet }

ALL_BITS == 2 ^ D - 1           \* bitmask with D low-order bits set

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)
VARIABLES towers

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)

(* Bitwise AND defined arithmetically: the result contains only the bits
   that are set in both arguments. *)
AND(x, y) == x - ((x - y) \* (y - x) \* 0)  \* placeholder; actual definition below

(* Proper arithmetic definition of AND for natural numbers up to 2^D-1 *)
BitAnd(x, y) == 
  IF x = 0 \/ y = 0 THEN 0
  ELSE
    LET hi == 2 ^ (D - 1) IN
      IF x >= hi /\ y >= hi THEN
        hi + BitAnd(x - hi, y - hi)
      ELSE IF x >= hi THEN
        BitAnd(x - hi, y)
      ELSE IF y >= hi THEN
        BitAnd(x, y - hi)
      ELSE
        BitAnd(x, y)

\* For readability we expose BitAnd as AND
AND == BitAnd

(* Returns the smallest disk present on tower t, or 0 if empty *)
SmallestDisk(t) ==
  IF towers[t] = 0 THEN 0
  ELSE
    IF towers[t] % 2 = 1 THEN 1
    ELSE
      LET k == 0 IN
        WHILE (towers[t] % (2 ^ (k + 1))) = 0 DO k := k + 1;
        2 ^ k

(* Predicate: disk d is the smallest on tower t *)
IsSmallestOn(d, t) == SmallestDisk(t) = d

(* Predicate: tower t has no disk smaller than d *)
NoSmallerOn(d, t) ==
  \A k \in DiskSet :
    (Disk(k) < d) => (AND(towers[t], Disk(k)) = 0)

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ towers = [t \in 1..N |-> IF t = 1 THEN ALL_BITS ELSE 0]

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next ==
  \E src \in 1..N, dst \in 1..N :
    /\ src # dst
    /\ \E d \in ALL_DISKS :
         /\ AND(towers[src], d) = d                \* disk d is on src
         /\ IsSmallestOn(d, src)                  \* d is smallest on src
         /\ NoSmallerOn(d, dst)                    \* dst has no smaller disk
         /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                      ![dst] = towers[dst] + d]

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<towers>>

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
  /\ \A t \in 1..N : towers[t] \in 0..ALL_BITS
  /\ \A t \in 1..N : towers[t] = 0 \/ 
       \E d \in ALL_DISKS : AND(towers[t], d) = d

Inv == 
  /\ \A t \in 1..N : towers[t] \in 0..ALL_BITS
  /\ \A i, j \in 1..N : i # j => (AND(towers[i], towers[j]) = 0)  \* disks are disjoint
  /\ \A t \in 1..N :
        \A d \in ALL_DISKS :
          IF AND(towers[t], d) = d THEN
            \A d2 \in ALL_DISKS :
              (d2 < d) => (AND(towers[t], d2) = 0)          \* no smaller disk beneath
          ELSE TRUE
  /\ \A t \in 1..N : towers[t] <= ALL_BITS
  /\ \A t \in 1..N : towers[t] >= 0
  /\ \A t \in 1..N : towers[t] \in Nat
  /\ \A t \in 1..N : towers[t] = 0 \/ \E d \in ALL_DISKS : AND(towers[t], d) = d
  /\ \A t \in 1..N : towers[t] \in Nat
  /\ \A t \in 1..N : towers[t] <= ALL_BITS
  /\ \A t \in 1..N : towers[t] >= 0
  /\ towers[1] + towers[2] + \E i \in 3..N : towers[i] = ALL_BITS

(***************************************************************************)
(* THEOREMS / ASSUMPTIONS (none needed for this spec)                     *)
(***************************************************************************)

=============================================================================