---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANT D, N

VARIABLE towers

\* Set of disk values (powers of two)
DiskSet == { 2 ^ k : k \in 0..D-1 }

\* Test whether disk d (a power of two) is present in tower value t
DiskPresent(t, d) == ((t \div d) % 2) = 1

\* Initial state: all disks on tower 1, others empty
Init == 
  towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* One legal move of the smallest disk on a source tower to a destination tower
Next ==
  \/ \E i \in 1..N:
      \E j \in 1..N:
        /\ i # j
        /\ \E d \in DiskSet:
            /\ DiskPresent(towers[i], d)          \* disk d is on source
            /\ (towers[i] % d) = 0                \* d is the smallest on source
            /\ (towers[j] % d) = 0                \* no smaller disk on dest
            /\ towers' = [towers EXCEPT 
                            ![i] = towers[i] - d,
                            ![j] = towers[j] + d]

\* Behaviour specification
Spec == Init /\ [][Next]_towers

\* Type correctness invariant
TypeOK == 
  /\ towers \in [1..N -> Nat]
  /\ \A i \in 1..N: towers[i] < 2 ^ D

\* Conservation invariant (all disks accounted for)
Inv == 
  /\ SUM i \in 1..N: towers[i] = (2 ^ D) - 1

====