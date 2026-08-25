---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

DiskVals == { 2 ^ (i - 1) : i \in 1..D }

AllDisks == 2 ^ D - 1

(* Disk d is present on tower value t *)
DiskOn(t, d) == (t % (2 * d)) >= d

(* Disk d is the smallest disk on tower t *)
SmallestOn(t, d) == DiskOn(t, d) /\ (t % d) = 0

(* No disk smaller than d is present on tower t *)
NoSmaller(t, d) == (t % d) = 0

LegalMove(d, s, dst) ==
    /\ s # dst
    /\ d \in DiskVals
    /\ SmallestOn(towers[s], d)
    /\ NoSmaller(towers[dst], d)

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)

Next ==
    \E d \in DiskVals: \E s \in 1..N: \E dst \in 1..N:
        /\ LegalMove(d, s, dst)
        /\ towers' = [towers EXCEPT
                        ![s]   = towers[s] - d,
                        ![dst] = towers[dst] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2 ^ D

Inv ==
    /\ \sum i \in 1..N: towers[i] = AllDisks

====