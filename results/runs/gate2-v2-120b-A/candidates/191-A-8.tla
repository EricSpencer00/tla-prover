---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

(*--------------------------------------------------------------------
  Derived constants
--------------------------------------------------------------------*)
DiskSet == 1 .. D
TowerSet == 1 .. N
AllDisks == 2 ^ D - 1

DiskOf(i) == 2 ^ (i - 1)

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
(* Convert a natural number to the set of disks (powers of two) whose bits are set *)
Bits(v) == { i \in DiskSet : (v % (2 ^ i)) >= (2 ^ (i - 1)) }

(* The smallest disk present on a tower, if any *)
SmallestDisk(t) ==
  LET s == \E i \in DiskSet : DiskOf(i) \in Bits(t) : i
  IN IF \E i \in DiskSet : DiskOf(i) \in Bits(t)
        THEN DiskOf(s)
        ELSE 0

(* All disks currently present on all towers *)
AllOnTowers == \A i \in DiskSet :
                  \E j \in TowerSet : DiskOf(i) \in Bits(towers[j])

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ towers = [j \in TowerSet |-> IF j = 1 THEN AllDisks ELSE 0]
  /\ \A j \in TowerSet : towers[j] \in 0 .. AllDisks

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)
Move ==
  \E d \in DiskSet, src \in TowerSet, dst \in TowerSet :
    /\ src # dst
    /\ DiskOf(d) \in Bits(towers[src])                \* disk is present at source
    /\ DiskOf(d) = SmallestDisk(towers[src])          \* it is the smallest on source
    /\ (towers[dst] = 0 \/ DiskOf(d) < SmallestDisk(towers[dst]))
    /\ towers' = [towers EXCEPT ![src] = towers[src] - DiskOf(d),
                                 ![dst] = towers[dst] + DiskOf(d)]

Next == Move

Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
TypeOK ==
  /\ towers \in [TowerSet -> 0 .. AllDisks]
  /\ \A j \in TowerSet : towers[j] < 2 ^ D

Inv ==
  /\ \A i \in DiskSet : DiskOf(i) \in \bigcup_{j \in TowerSet} Bits(towers[j])
  /\ \A j \in TowerSet : towers[j] \in 0 .. AllDisks
  /\ \A i \in DiskSet : DiskOf(i) <= AllDisks
  /\ \A i \in DiskSet :
        \E j \in TowerSet : DiskOf(i) \in Bits(towers[j])
  /\ \A i \in DiskSet, j \in TowerSet :
        (DiskOf(i) \in Bits(towers[j]) =>
         \A k \in DiskSet :
            k < i => DiskOf(k) \notin Bits(towers[j]))
  /\ \A i \in DiskSet :
        DiskOf(i) \in Bits(towers[1]) \/ DiskOf(i) \in Bits(towers[N])
  /\ \A i \in DiskSet :
        (i = D) => DiskOf(i) \in Bits(towers[N])
  /\ \A j \in TowerSet : Sum({ DiskOf(i) : i \in DiskSet /\ DiskOf(i) \in Bits(towers[j]) }) = towers[j]

(*--------------------------------------------------------------------
  Theorem (optional, for TLC)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====