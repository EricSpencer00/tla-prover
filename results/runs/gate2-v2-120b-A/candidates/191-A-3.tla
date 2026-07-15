---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT D \* number of disks (must be >= 1)
CONSTANT N \* number of towers (must be >= 2)

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
DISKS == 1 .. D                \* indices for disks, smallest disk is 1
VALUES == { 2^k : k \in DISKS } \* actual disk sizes (powers of two)

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES towers          \* function [1..N -> Nat] encoding tower contents

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
DiskVals == { 2^k : k \in DISKS }   \* set of all possible disk values

Mask(i) == 2^(i-1)                  \* value of the i-th (smallest) disk
TopMask(A) == 
    IF A = 0 THEN 0 ELSE 
        2 ^ ( 1 + LogBase2( A - 1 ) )   \* highest power of two <= A

(* LogBase2 returns the floor of the base‑2 logarithm of a positive integer.
   It is defined using recursion over the natural numbers. *)
LogBase2(0) == 0
LogBase2(n) == 
    IF n = 1 THEN 0 ELSE 1 + LogBase2( n \div 2 )

(* Bitwise AND expressed in pure arithmetic.
   AND(x, y) = sum of those powers of two that appear in both x and y. *)
AND(x, y) == 
    IF x = 0 \/ y = 0 THEN 0 ELSE
        LET hi == TopMask(x) IN
        IF hi \in DiskVals /\ hi \in DiskVals /\ (hi <= y) THEN
            hi + AND( x - hi, y - hi )
        ELSE
            AND( x - hi, y )

(* The smallest disk present on a non‑empty tower is its least‑significant bit. *)
Smallest(t) == 
    IF t = 0 THEN 0 ELSE 
        2 ^ ( LogBase2( t ) )

(* Sum of all tower values *)
Total == \Sum_{i \in 1..N} towers[i]

(* Goal: all disks are on the last tower *)
Goal == towers[N] = 2^D - 1

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]
    /\ Total = 2^D - 1

(*--------------------------------------------------------------------
  Move action (nondeterministic)
--------------------------------------------------------------------*)
Move ==
    \E src \in 1..N, dst \in 1..N, d \in DiskVals :
        /\ src # dst
        /\ towers[src] # 0
        /\ (towers[src] AND d) = d               \* disk d is present on src
        /\ d = Smallest(towers[src])             \* d is the top disk on src
        /\ (towers[dst] # 0 => Smallest(towers[dst]) > d)   \* dst top larger
        /\ towers' = [towers EXCEPT 
                        ![src] = towers[src] - d,
                        ![dst] = towers[dst] + d]

Next == Move

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
TypeOK == 
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2^D

Inv == Total = 2^D - 1

(*--------------------------------------------------------------------
  Liveness (none required)
--------------------------------------------------------------------*)

====