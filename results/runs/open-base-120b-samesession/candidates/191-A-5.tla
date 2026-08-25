---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* ----------------------------------------------------------------------
   Disk definition: each disk size is a distinct power of two.
   ---------------------------------------------------------------------- *)
Disk(i) == 2 ^ i

DiskSet == { Disk(i) : i \in 0..D-1 }

(* ----------------------------------------------------------------------
   Bit‐wise test (using arithmetic).  d is a power of two.
   ---------------------------------------------------------------------- *)
IsSet(t, d) == (t \div d) % 2 = 1

(* ----------------------------------------------------------------------
   The smallest disk present on a tower (0 if the tower is empty).
   ---------------------------------------------------------------------- *)
SmallestOn(t) ==
  IF t = 0 THEN 0
  ELSE
    CHOOSE d \in DiskSet :
      IsSet(t, d) /\ (\A d2 \in DiskSet : d2 < d => ~IsSet(t, d2))

(* ----------------------------------------------------------------------
   Initial state: all disks on tower 1, others empty.
   ---------------------------------------------------------------------- *)
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]
  /\ TypeOK

(* ----------------------------------------------------------------------
   Type correctness: each tower value is a natural number < 2^D.
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ \A i \in 1..N : towers[i] \in Nat
  /\ \A i \in 1..N : towers[i] < 2 ^ D

(* ----------------------------------------------------------------------
   Safety invariant: type correctness plus conservation of total disks.
   ---------------------------------------------------------------------- *)
Inv ==
  /\ TypeOK
  /\ Sum({ towers[i] : i \in 1..N }) = 2 ^ D - 1

(* ----------------------------------------------------------------------
   One legal move: move disk d from src to dst.
   ---------------------------------------------------------------------- *)
Move(d, src, dst) ==
  /\ d \in DiskSet
  /\ src \in 1..N /\ dst \in 1..N /\ src # dst
  /\ IsSet(towers[src], d)                                   \* disk present
  /\ (\A d2 \in DiskSet : d2 < d => ~IsSet(towers[src], d2)) \* smallest on src
  /\ (\A d2 \in DiskSet : d2 < d => ~IsSet(towers[dst], d2)) \* no smaller on dst
  /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                              ![dst] = towers[dst] + d]

(* ----------------------------------------------------------------------
   Next-state relation: any legal move may occur.
   ---------------------------------------------------------------------- *)
Next ==
  \E d \in DiskSet :
    \E src \in 1..N :
      \E dst \in 1..N :
        Move(d, src, dst)

(* ----------------------------------------------------------------------
   Specification: init followed by any number of moves.
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [] [Next]_<<towers>>

====