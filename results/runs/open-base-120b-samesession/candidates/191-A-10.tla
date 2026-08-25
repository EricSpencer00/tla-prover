---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
  DiskSet: the set of all disk values, each a distinct power of two.
-----------------------------------------------------------------*)
DiskSet == { 2^k : k \in 0..(D-1) }

(*-----------------------------------------------------------------
  DiskOn(twr, d) is TRUE iff disk d (a power of two) is present on
  tower value twr.  The test uses arithmetic modulo: the bit for d
  is set when the remainder of twr divided by 2*d is at least d.
-----------------------------------------------------------------*)
DiskOn(twr, d) == (twr % (2 * d)) >= d

(*-----------------------------------------------------------------
  Init: all disks are on the first tower, all others are empty.
-----------------------------------------------------------------*)
Init ==
    /\ towers[1] = (2^D) - 1
    /\ \A i \in 2..N: towers[i] = 0
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \Sum i \in 1..N: towers[i] = (2^D) - 1

(*-----------------------------------------------------------------
  Next: nondeterministically pick a smallest movable disk and move it
  from a source tower s to a distinct destination tower t, respecting
  the Tower of Hanoi rules.
-----------------------------------------------------------------*)
Next ==
    \E d \in DiskSet:
      \E s \in 1..N:
        \E t \in 1..N:
          /\ s # t
          /\ DiskOn(towers[s], d)          \* disk d is on source
          /\ towers[s] % d = 0            \* d is the smallest on source
          /\ towers[t] % d = 0            \* no smaller disk on dest
          /\ towers' = [towers EXCEPT
                         ![s] = towers[s] - d,
                         ![t] = towers[t] + d]

(*-----------------------------------------------------------------
  Spec: the usual temporal specification (init and always-next).
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_towers

(*-----------------------------------------------------------------
  TypeOK: each tower value is a natural number less than 2^D.
-----------------------------------------------------------------*)
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2^D

(*-----------------------------------------------------------------
  Inv: the conservation invariant – the sum of all tower values is
  always 2^D - 1 (all disks accounted for).
-----------------------------------------------------------------*)
Inv == \Sum i \in 1..N: towers[i] = (2^D) - 1

====