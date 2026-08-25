---- MODULE Hanoi ----
EXTENDS Naturals, TLC, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* The set of disks, each represented by a distinct power of two *)
Disk == { 2 ^ k : k \in 0..D-1 }

(* Helper predicates using arithmetic in place of bitwise operators *)
DiskOn(t, d) == (t % (2 * d) >= d)          \* disk d is present on tower t
NoSmallerOn(t, d) == (t % d = 0)            \* no disk smaller than d is on tower t

(* Initial state: all disks on the first tower *)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = (2 ^ D) - 1
    /\ \A i \in 2..N: towers[i] = 0

(* One legal move: move the smallest disk on a source tower to a destination tower *)
Next ==
    \E d \in Disk:
        \E src \in 1..N:
            \E dst \in 1..N:
                /\ src # dst
                /\ DiskOn(towers[src], d)          \* d is on src
                /\ NoSmallerOn(towers[src], d)     \* d is the smallest on src
                /\ NoSmallerOn(towers[dst], d)     \* dst has no smaller disk
                /\ towers' = [towers EXCEPT
                                ![src] = towers[src] - d,
                                ![dst] = towers[dst] + d]

(* Temporal specification *)
Spec == Init /\ [][Next]_towers

(* Type correctness invariant *)
TypeOK ==
    /\ \A i \in 1..N: towers[i] \in Nat
    /\ \A i \in 1..N: towers[i] < 2 ^ D

(* Conservation invariant *)
Inv ==
    Sum(i \in 1..N, towers[i]) = (2 ^ D) - 1

====