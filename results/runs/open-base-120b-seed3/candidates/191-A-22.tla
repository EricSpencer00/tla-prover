---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLE towers

(*--------------------------------------------------------------------
  Disk representation: each disk size is a distinct power of two.
--------------------------------------------------------------------*)
DiskSet == { 2^i : i \in 0..(D-1) }

AllDisks == 2^D - 1

(*--------------------------------------------------------------------
  Helper predicates
--------------------------------------------------------------------*)
DiskPresent(v, d) == ((v \div d) % 2) = 1

SmallestOn(v, d) ==
    DiskPresent(v, d) /\ \A e \in DiskSet : (e < d) => ~DiskPresent(v, e)

DestOK(v, d) ==
    \A e \in DiskSet : (e < d) => ~DiskPresent(v, e)

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = AllDisks
    /\ \A i \in 1..N : (i # 1) => towers[i] = 0

(*--------------------------------------------------------------------
  Next-state relation (a legal move)
--------------------------------------------------------------------*)
Next ==
    \E d \in DiskSet :
        \E src, dst \in 1..N :
            /\ src # dst
            /\ DiskPresent(towers[src], d)
            /\ SmallestOn(towers[src], d)
            /\ DestOK(towers[dst], d)
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
    /\ \A i \in 1..N : towers[i] < 2^D

Inv ==
    \Sum i \in 1..N : towers[i] = AllDisks

====