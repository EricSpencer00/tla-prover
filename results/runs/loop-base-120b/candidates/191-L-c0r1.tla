---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLE t

(*--------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------*)

AllDisks == 2^D - 1

DiskSet == { 2^k : k \in 0..(D-1) }

(* Disk d is present in tower value v *)
HasDisk(v, d) == ((v \div d) % 2) = 1

(* d is the smallest disk on a tower with value v *)
IsSmallest(d, v) == HasDisk(v, d) /\ (v % d) = 0

(* Destination tower v can receive disk d (no smaller disk present) *)
DestOk(d, v) == (v % d) = 0

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ \A i \in 1..N: t[i] \in Nat
    /\ \A i \in 1..N: t[i] < 2^D

(*--------------------------------------------------------------------
  Conservation invariant
--------------------------------------------------------------------*)
Inv ==
    Sum({i \in 1..N}, t[i]) = AllDisks

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ t = [i \in 1..N |-> IF i = 1 THEN AllDisks ELSE 0]
    /\ TypeOK

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \E d \in DiskSet:
        \E s \in 1..N:
            \E d2 \in 1..N:
                /\ s # d2
                /\ IsSmallest(d, t[s])
                /\ DestOk(d, t[d2])
                /\ t' = [t EXCEPT ![s] = t[s] - d,
                                 ![d2] = t[d2] + d]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_t

====