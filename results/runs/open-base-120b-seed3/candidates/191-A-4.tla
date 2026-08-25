---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

VARIABLES towers

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

(* Set of disks, each represented by a distinct power of two *)
DiskSet == { 2^i : i \in 0..(D-1) }

(* Test whether disk d (a power of two) is present on tower value t *)
IsSet(t, d) == (t \div d) % 2 = 1

(*--------------------------------------------------------------------
  State definition
--------------------------------------------------------------------*)

Init ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N :
          IF i = 1 THEN towers[i] = (2^D) - 1
          ELSE towers[i] = 0

(*--------------------------------------------------------------------
  Move action
--------------------------------------------------------------------*)

Move(d, s, dst) ==
    /\ d \in DiskSet
    /\ s \in 1..N
    /\ dst \in 1..N
    /\ s # dst
    /\ IsSet(towers[s], d)                         \* disk is on source
    /\ \A e \in DiskSet : e < d => ~IsSet(towers[s], e)   \* d is smallest on source
    /\ \A e \in DiskSet : e < d => ~IsSet(towers[dst], e)  \* no smaller on dest
    /\ towers' = [towers EXCEPT
                    ![s]   = towers[s] - d,
                    ![dst] = towers[dst] + d]

Next ==
    \E d \in DiskSet: \E s \in 1..N: \E dst \in 1..N: Move(d, s, dst)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<towers>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)

TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < (2^D)

Inv ==
    (+/ i \in 1..N : towers[i]) = (2^D) - 1

=============================================================================