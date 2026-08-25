---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*-------------------------------------------------------------------*)
(* Helper definitions *)

(* The set of disk sizes, each a distinct power of two *)
DiskSet == { 2 ^ k : k \in 0..(D-1) }

(* All disks together, represented as a bitmask *)
AllBits == 2 ^ D - 1

(* Test whether a particular disk d is present on tower t *)
DiskPresent(t, d) == (towers[t] % (2 * d)) >= d

(* The smallest disk on a given tower (if any) *)
SmallestDisk(t) ==
  IF towers[t] = 0
    THEN 0
    ELSE CHOOSE d \in DiskSet :
            DiskPresent(t, d) /\ 
            \A e \in DiskSet : e < d => ~DiskPresent(t, e)

(*-------------------------------------------------------------------*)
(* Initial state *)

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN AllBits ELSE 0]
  /\ \A i \in 1..N : towers[i] \in Nat

(*-------------------------------------------------------------------*)
(* Next-state relation *)

LegalMove ==
  \E src, dst \in 1..N :
    /\ src # dst
    /\ \E d \in DiskSet :
         /\ DiskPresent(src, d)                         \* disk is on source
         /\ \A e \in DiskSet : e < d => ~DiskPresent(src, e)   \* smallest on source
         /\ \A e \in DiskSet : e < d => ~DiskPresent(dst, e)   \* no smaller on dest
         /\ towers' = [towers EXCEPT 
                         ![src] = towers[src] - d,
                         ![dst] = towers[dst] + d]

Next == LegalMove

(*-------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_towers

(*-------------------------------------------------------------------*)
(* Invariants *)

(* Type correctness: each tower value is a natural number < 2^D *)
TypeOK ==
  \A i \in 1..N : towers[i] \in Nat /\ towers[i] < 2 ^ D

(* Conservation: total of all tower values equals AllBits *)
Inv ==
  Sum(i \in 1..N : towers[i]) = AllBits

=============================================================================