---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
  Disk values are powers of two: 1, 2, 4, ..., 2^(D-1)
-----------------------------------------------------------------*)
DiskValues == { 2 ^ (k - 1) : k \in 1..D }

AllDisksMask == 2 ^ D - 1

(*-----------------------------------------------------------------
  Bit test: true iff the bit corresponding to disk d (a power of two)
  is set in value v.
-----------------------------------------------------------------*)
IsSet(v, d) == (v % (2 * d) >= d)

(*-----------------------------------------------------------------
  d is the smallest disk on tower t
-----------------------------------------------------------------*)
SmallestOn(t, d) ==
    IsSet(towers[t], d) /\ 
    \A e \in DiskValues : (e < d => ~IsSet(towers[t], e))

(*-----------------------------------------------------------------
  No disk smaller than d is present on tower t
-----------------------------------------------------------------*)
NoSmaller(t, d) ==
    \A e \in DiskValues : (e < d => ~IsSet(towers[t], e))

(*-----------------------------------------------------------------
  Initial state: all disks on tower 1, others empty
-----------------------------------------------------------------*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN AllDisksMask ELSE 0]

(*-----------------------------------------------------------------
  One legal move
-----------------------------------------------------------------*)
Move ==
    \E src, dst \in 1..N :
        \E d \in DiskValues :
            /\ src # dst
            /\ SmallestOn(src, d)
            /\ NoSmaller(dst, d)
            /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                      ![dst] = towers[dst] + d]

Next == Move

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
TypeOK ==
    \A i \in 1..N :
        towers[i] \in Nat /\ towers[i] < 2 ^ D

Inv ==
    \Sum i \in 1..N: towers[i] = AllDisksMask
====