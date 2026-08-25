---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Maximum value representing all disks *)
MaxMask == 2^D - 1

(* Set of disk values (powers of two) *)
Disk == { 2^i : i \in 0..D-1 }

(* Helper predicates using arithmetic on the bitwise encoding *)
IsOn(t, d) == ((t DIV d) % 2) = 1
SmallestOn(t, d) == t % d = 0
NoSmaller(t, d) == t % d = 0

(* Initial state: all disks on the first tower, others empty *)
Init ==
   /\ towers \in [1..N -> Nat]
   /\ towers[1] = MaxMask
   /\ \A i \in (1..N) \ {1} : towers[i] = 0

(* One legal move of a single disk *)
Next ==
   \E d \in Disk, src \in 1..N, dst \in 1..N :
      /\ src # dst
      /\ IsOn(towers[src], d)
      /\ SmallestOn(towers[src], d)
      /\ NoSmaller(towers[dst], d)
      /\ towers' = [towers EXCEPT ![src] = towers[src] - d,
                               ![dst] = towers[dst] + d]

(* Specification *)
Spec == Init /\ [][Next]_towers

(* Type correctness invariant *)
TypeOK ==
   /\ towers \in [1..N -> Nat]
   /\ \A i \in 1..N : towers[i] \in 0..MaxMask

(* Conservation invariant: all disks are always accounted for *)
Inv == (∑ i \in 1..N : towers[i]) = MaxMask

====