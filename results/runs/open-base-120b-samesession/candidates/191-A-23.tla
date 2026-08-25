---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Disk representation and helper definitions
--------------------------------------------------------------------*)
DiskSet == { 2 ^ k : k \in 0..D-1 }

MaxVal == 2 ^ D - 1

DiskPresent(d, t) == (towers[t] \div d) mod 2 = 1

NoSmallerOn(t, d) == \A e \in DiskSet : e < d => ~DiskPresent(e, t)

SmallestOn(t, d) == DiskPresent(d, t) /\ NoSmallerOn(t, d)

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    towers = [i \in 1..N |-> IF i = 1 THEN MaxVal ELSE 0]

(*--------------------------------------------------------------------
  Next-state relation (legal moves)
--------------------------------------------------------------------*)
Next ==
    \E d \in DiskSet :
        \E s \in 1..N :
            \E t \in 1..N :
                s # t /\ SmallestOn(s, d) /\ NoSmallerOn(t, d) /\
                towers' = [towers EXCEPT ![s] = towers[s] - d,
                                         ![t] = towers[t] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..MaxVal

Inv ==
    /\ \Sum i \in 1..N : towers[i] = MaxVal

====