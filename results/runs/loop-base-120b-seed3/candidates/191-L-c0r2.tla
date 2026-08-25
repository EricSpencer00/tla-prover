---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT D, N

VARIABLES towers

(*-----------------------------------------------------------------
  Set of disks, each represented by a distinct power of two.
-----------------------------------------------------------------*)
Disk == { 2^i : i \in 0..D-1 }

AllDisks == 2^D - 1

(*-----------------------------------------------------------------
  Initial state: all disks on tower 1, all other towers empty.
-----------------------------------------------------------------*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisks
    /\ \A i \in 1..N : (i # 1) => towers[i] = 0

(*-----------------------------------------------------------------
  Helper predicates for the move relation.
-----------------------------------------------------------------*)
DiskPresent(t, d) == (towers[t] % (2 * d)) >= d
SmallestOn(t, d)  == (towers[t] % d) = 0
NoSmallerOn(t, d) == (towers[t] % d) = 0

(*-----------------------------------------------------------------
  A legal move: pick a source, a destination, and a disk that is
  the smallest on the source and can be placed on the destination.
-----------------------------------------------------------------*)
Move ==
    \E src \in 1..N, dst \in 1..N, d \in Disk :
        /\ src # dst
        /\ DiskPresent(src, d)          \* the disk is on the source tower
        /\ SmallestOn(src, d)           \* it is the smallest disk there
        /\ NoSmallerOn(dst, d)          \* destination has no smaller disk
        /\ towers' = [t \in 1..N |-> 
                IF t = src THEN towers[t] - d
                ELSE IF t = dst THEN towers[t] + d
                ELSE towers[t]]

Next == Move

(*-----------------------------------------------------------------
  Type correctness: every tower value is a natural number less than 2^D.
-----------------------------------------------------------------*)
TypeOK ==
    /\ \A t \in 1..N : towers[t] \in Nat
    /\ \A t \in 1..N : towers[t] < 2^D

(*-----------------------------------------------------------------
  Safety invariant: the total sum of all tower values is constant.
-----------------------------------------------------------------*)
Inv ==
    /\ \A t \in 1..N : towers[t] \in Nat
    /\ \SUM t \in 1..N : towers[t] = AllDisks

(*-----------------------------------------------------------------
  The full specification.
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

====