---- MODULE Hanoi ----
EXTENDS Naturals, TLC

CONSTANTS D, N

\* The set of disk sizes, each a distinct power of two.
Disk == { 2 ^ i : i \in 0..(D - 1) }

\* Helper predicate: a natural number is a power of two (or zero).
IsPowerOfTwo(x) == x = 0 \/ \E i \in 0..(D-1) : x = 2 ^ i

\* The total value representing all disks.
Total == 2 ^ D - 1

VARIABLES towers

\* towers is a function mapping each tower index (1..N) to a natural number.
\* The value of a tower encodes the disks present using bits.
Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN Total ELSE 0]
    /\ TypeOK

\* Type correctness: each tower value is a natural less than 2^D.
TypeOK ==
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] \in 0..Total
    /\ \A i \in 1..N : \A d \in Disk :
           ( (towers[i] /\ d) = d ) => d \in Disk   \* bits correspond to valid disks

\* The smallest disk on a non‑empty tower is the least‑significant set bit.
Smallest(t) ==
    IF t = 0 THEN 0
    ELSE 2 ^ (CHOOSE i \in 0..(D-1) : (t /\ (2 ^ i)) # 0)

\* A move selects a disk d, a source tower s, and a destination tower dst,
\* and updates the towers accordingly.
Move ==
    \E d \in Disk :
    \E s \in 1..N :
    \E dst \in 1..N :
        /\ s # dst
        /\ (towers[s] /\ d) = d                     \* d is present on source
        /\ d = Smallest(towers[s])                  \* d is the smallest on source
        /\ (towers[dst] = 0 \/ Smallest(towers[dst]) # d)  \* no smaller disk on dest
        /\ towers' = [towers EXCEPT ![s] = towers[s] - d,
                                   ![dst] = towers[dst] + d]

\* Next relation: either a legal move occurs or the state stutters.
Next == Move \/ UNCHANGED towers

\* Safety invariant: the total sum of all tower values is conserved.
Inv == \A i \in 1..N : towers[i] \in 0..Total
       /\ \A i \in 1..N : \A d \in Disk : ( (towers[i] /\ d) = d ) => d \in Disk
       /\ \Sum i \in 1..N : towers[i] = Total

Spec == Init /\ [][Next]_<<towers>>

====