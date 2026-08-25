---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(*-----------------------------------------------------------------
  Disk values are powers of two: 1, 2, 4, ..., 2^(D-1)
-----------------------------------------------------------------*)
DiskValues == { 2 ^ k : k \in 0..D-1 }

(*-----------------------------------------------------------------
  Test whether disk d (a power of two) is present on tower t.
  Since d is a power of two, its presence can be detected by checking
  the k‑th bit of towers[t], i.e., ((towers[t] DIV d) % 2) = 1.
-----------------------------------------------------------------*)
IsOn(t, d) == ((towers[t] DIV d) % 2) = 1

(*-----------------------------------------------------------------
  Initial state: all disks on the first tower, others empty.
-----------------------------------------------------------------*)
Init ==
  /\ towers \in [1..N -> Nat]
  /\ towers[1] = (2 ^ D) - 1
  /\ \A i \in 2..N: towers[i] = 0

(*-----------------------------------------------------------------
  One legal move: move the smallest disk on a source tower to a
  destination tower where no smaller disk is present.
-----------------------------------------------------------------*)
Move ==
  \E src \in 1..N :
    \E dst \in 1..N :
      /\ src # dst
      /\ \E d \in DiskValues :
            /\ IsOn(src, d)                                 \* disk is on source
            /\ \A d2 \in DiskValues : d2 < d => ~IsOn(src, d2)   \* smallest on source
            /\ \A d2 \in DiskValues : d2 < d => ~IsOn(dst, d2)   \* no smaller on dest
            /\ towers' = [towers EXCEPT
                            ![src] = towers[src] - d,
                            ![dst] = towers[dst] + d]

Next == Move \/ UNCHANGED towers

Spec == Init /\ [][Next]_towers

(*-----------------------------------------------------------------
  Safety properties
-----------------------------------------------------------------*)
TypeOK ==
  /\ \A i \in 1..N : towers[i] \in Nat
  /\ \A i \in 1..N : towers[i] < 2 ^ D

Inv ==
  (+/ i \in 1..N : towers[i]) = (2 ^ D) - 1

====