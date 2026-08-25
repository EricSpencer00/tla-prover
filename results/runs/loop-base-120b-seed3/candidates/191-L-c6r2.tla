---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

DiskVals == { 2^(k-1) : k \in 1..D }

AllDisks == 2^D - 1

(* Disk d is present on tower t *)
DiskOn(t, d) == ((towers[t] \div d) % 2) = 1

(* No disk smaller than d is present on tower t *)
NoSmaller(t, d) == \A e \in DiskVals : e < d => ~DiskOn(t, e)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]

(*--------------------------------------------------------------------
  Next-state relation (one legal move)
--------------------------------------------------------------------*)
Next ==
    \E src \in 1..N :
      \E dst \in 1..N :
        \E d \in DiskVals :
          /\ src # dst
          /\ DiskOn(src, d)
          /\ NoSmaller(src, d)          \* d is the smallest on source
          /\ NoSmaller(dst, d)          \* destination has no smaller disk
          /\ towers' = [towers EXCEPT
                          ![src] = towers[src] - d,
                          ![dst] = towers[dst] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..AllDisks

Inv ==
    (\sum i \in 1..N : towers[i]) = AllDisks

====