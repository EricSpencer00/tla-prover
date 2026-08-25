---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Disk set: powers of two from 2^0 up to 2^(D-1)
--------------------------------------------------------------------*)
DiskSet == { 2^k : k \in 0..(D-1) }

(*--------------------------------------------------------------------
  Helper predicates for bitwise reasoning using arithmetic
--------------------------------------------------------------------*)
(* disk d is present on tower value t *)
On(t, d) == (t % (2 * d) >= d)

(* tower t has no disk smaller than d (i.e., all lower-order bits are zero) *)
NoSmaller(t, d) == (t % d = 0)

(*--------------------------------------------------------------------
  Initial state: all disks on the first tower, others empty
--------------------------------------------------------------------*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = 2^D - 1
    /\ \A i \in 2..N: towers[i] = 0

(*--------------------------------------------------------------------
  Move action: move a smallest disk from source i to destination j
--------------------------------------------------------------------*)
Move(i, j, d) ==
    /\ i \in 1..N
    /\ j \in 1..N
    /\ i # j
    /\ d \in DiskSet
    /\ On(towers[i], d)               \* disk d is on source
    /\ NoSmaller(towers[i], d)        \* d is the smallest on source
    /\ NoSmaller(towers[j], d)        \* destination has no smaller disk
    /\ towers' = [towers EXCEPT
                    ![i] = towers[i] - d,
                    ![j] = towers[j] + d]

Next ==
    \E i, j \in 1..N: \E d \in DiskSet: Move(i, j, d)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

(*--------------------------------------------------------------------
  Conservation invariant: sum of all tower values equals total disks
--------------------------------------------------------------------*)
Inv ==
    (+/ i \in 1..N: towers[i]) = 2^D - 1

====