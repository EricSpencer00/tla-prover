---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
  Disk values are powers of two: 1, 2, 4, … , 2^(D‑1)
-----------------------------------------------------------------*)
DiskSet == { 2 ^ i : i \in 0..(D-1) }

(*-----------------------------------------------------------------
  Type correctness: each tower holds a natural number less than 2^D
-----------------------------------------------------------------*)
TypeOK == /\ \A i \in 1..N: towers[i] \in Nat
          /\ \A i \in 1..N: towers[i] < 2 ^ D

(*-----------------------------------------------------------------
  Conservation: the sum of all tower values always equals
  the total number of disks (2^D‑1)
-----------------------------------------------------------------*)
Total == 2 ^ D - 1
Consistent == \Sum i \in 1..N: towers[i] = Total

(*-----------------------------------------------------------------
  Combined invariant required by the .cfg file
-----------------------------------------------------------------*)
Inv == TypeOK /\ Consistent

(*-----------------------------------------------------------------
  Initial state: all disks on the first tower, others empty
-----------------------------------------------------------------*)
Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN Total ELSE 0]
        /\ Consistent   \* holds trivially for the initial mapping

(*-----------------------------------------------------------------
  Helper predicates for the move legality
-----------------------------------------------------------------*)
IsSmallest(d, t) == (t % (2 * d)) = d          \* d is present and no smaller disk on t
NoSmaller(t, d)  == (t % d) = 0                \* no disk smaller than d on t

(*-----------------------------------------------------------------
  Next-state relation: nondeterministically choose a legal move
-----------------------------------------------------------------*)
Next ==
  \E d \in DiskSet:
    \E s \in 1..N:
      \E dst \in 1..N:
        /\ s # dst
        /\ IsSmallest(d, towers[s])
        /\ NoSmaller(towers[dst], d)
        /\ towers' = [i \in 1..N |
                        IF i = s THEN towers[i] - d
                        ELSE IF i = dst THEN towers[i] + d
                        ELSE towers[i]]

(*-----------------------------------------------------------------
  Full specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<towers>>

====