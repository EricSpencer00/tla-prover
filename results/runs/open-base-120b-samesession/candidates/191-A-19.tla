---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Set of disk values, each a distinct power of two *)
DiskSet == { 2^i : i \in 0..(D-1) }

(* Helper predicates for bitwise tests using arithmetic *)
IsOn(val, d) == ((val \div d) % 2) = 1
LowerBitsZero(val, d) == (val % d) = 0

(* Initial state: all disks on tower 1, other towers empty *)
Init ==
    /\ towers \in [1..N -> Nat]
    /\ towers[1] = (2^D) - 1
    /\ \A i \in 2..N: towers[i] = 0
    /\ \A i \in 1..N: towers[i] >= 0
    /\ \A i \in 1..N: towers[i] < 2^D

(* One legal move of a smallest disk from a source tower to a destination tower *)
Next ==
    \E d \in DiskSet:
      \E s, t \in 1..N:
        /\ s # t
        /\ IsOn(towers[s], d)                \* disk d is present on source
        /\ LowerBitsZero(towers[s], d)       \* d is the smallest disk on source
        /\ LowerBitsZero(towers[t], d)       \* destination has no smaller disk
        /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![t] = towers[t] + d]

(* Specification *)
Spec == Init /\ [][Next]_<<towers>>

(* Type correctness invariant *)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N: towers[i] < 2^D

(* Conservation invariant: all disks are always accounted for *)
Total == +/ i \in 1..N: towers[i]
Inv == Total = (2^D) - 1

====