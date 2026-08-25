---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

(* Set of disk values, each a distinct power of two *)
DiskVals == { 2 ^ i : i \in 0..D-1 }

(* Disk d is present on a tower whose encoded value is v *)
DiskOn(v, d) == ((v \div d) % 2) = 1

(* No disk smaller than d is present on a tower whose encoded value is v *)
NoSmaller(v, d) == \A e \in DiskVals : e < d => ~DiskOn(v, e)

(* Predicate describing a legal move of disk d from source s to destination t *)
Move(d, s, t) ==
    /\ d \in DiskVals
    /\ s \in 1..N
    /\ t \in 1..N
    /\ s # t
    /\ DiskOn(towers[s], d)
    /\ NoSmaller(towers[s], d)
    /\ NoSmaller(towers[t], d)

(* Initial configuration: all disks on the first tower *)
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

(* One legal move may be performed nondeterministically *)
Next ==
    \E d \in DiskVals :
      \E s \in 1..N :
        \E t \in 1..N :
          /\ Move(d, s, t)
          /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![t] = towers[t] + d]

(* Type correctness: every tower value is a natural less than 2^D *)
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] >= 0 /\ towers[i] < 2 ^ D

(* Invariant: type correctness and conservation of total disks *)
Inv ==
    /\ TypeOK
    /\ Sum(i \in 1..N : towers[i]) = (2 ^ D) - 1

(* Full specification *)
Spec == Init /\ [][Next]_towers

====