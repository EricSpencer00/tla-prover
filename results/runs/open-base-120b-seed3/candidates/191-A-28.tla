---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Set of disks, each represented by a distinct power of two *)
Disk == { 2 ^ i : i \in 0..D-1 }

(* Disks smaller than a given disk *)
SmallerDisks(d) == { e \in Disk : e < d }

(* Test whether disk d is present on tower t *)
DiskOn(t, d) == ((towers[t] DIV d) % 2) = 1

(* Disk d is the smallest (topmost) disk on tower t *)
IsSmallest(t, d) == DiskOn(t, d) /\ \A e \in SmallerDisks(d) : ~DiskOn(t, e)

(* Tower t can receive disk d (no smaller disk is present) *)
CanPlace(t, d) == \A e \in SmallerDisks(d) : ~DiskOn(t, e)

(* Initial state: all disks on the first tower *)
Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

(* Type correctness: each tower value is a natural number < 2^D *)
TypeOK ==
  /\ towers \in [1..N -> Nat]
  /\ \A i \in 1..N : towers[i] < (2 ^ D)

(* Conservation invariant: total sum of disks is constant *)
Inv ==
  /\ TypeOK
  /\ Sum(i \in 1..N, towers[i]) = (2 ^ D) - 1

(* One legal move: move the smallest disk from src to dst *)
Move ==
  \E d \in Disk :
    \E src \in 1..N :
      \E dst \in 1..N :
        /\ src # dst
        /\ IsSmallest(src, d)
        /\ CanPlace(dst, d)
        /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                                   ![dst] = towers[dst] + d]

Next == Move

Spec == Init /\ [][Next]_towers

====