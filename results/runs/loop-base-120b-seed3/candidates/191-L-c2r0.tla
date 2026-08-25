---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

Disk(i) == 2 ^ i

Disks == { Disk(k) : k \in 0..D-1 }

(* test if disk d (a power of two) is present on tower value t *)
Present(t, d) == ((t \div d) % 2) = 1

(* test that tower value t has no disk smaller than d *)
NoSmaller(t, d) == t % d = 0

(* total number of disks expressed as a bitmask *)
ALLDISKS == 2 ^ D - 1

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN ALLDISKS ELSE 0]

(*--------------------------------------------------------------------
  Next-state relation (a legal move)
--------------------------------------------------------------------*)
Next ==
    \E d \in Disks, src \in 1..N, dst \in 1..N :
        /\ src # dst
        /\ Present(towers[src], d)          \* the disk is on the source tower
        /\ NoSmaller(towers[src], d)        \* it is the smallest on source
        /\ NoSmaller(towers[dst], d)        \* destination has no smaller disk
        /\ towers' = [i \in 1..N |->
                IF i = src THEN towers[src] - d
                ELSE IF i = dst THEN towers[dst] + d
                ELSE towers[i]]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..ALLDISKS

Inv ==
    \* Conservation of all disks
    \Sum_{i \in 1..N} towers[i] = ALLDISKS

====