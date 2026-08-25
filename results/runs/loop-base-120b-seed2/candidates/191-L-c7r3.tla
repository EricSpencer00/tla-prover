---- MODULE Hanoi ----
EXTENDS Naturals, Sequences, Bitwise, FiniteSets

CONSTANTS D, N

VARIABLES towers

\* Set of disk values (each a distinct power of two)
Disk == { 2 ^ i : i \in 0..D-1 }

\* The smallest disk on a tower t is d iff d is present and no smaller disk is present
IsSmallest(d, t) == 
    (BAnd(t, d) = d) /\ 
    \A d2 \in Disk : d2 < d => BAnd(t, d2) = 0

\* Destination tower must contain no disk smaller than d
NoSmaller(d, t) == 
    \A d2 \in Disk : d2 < d => BAnd(t, d2) = 0

\* One legal move: move the smallest disk d from source s to destination dst
Move == 
    \E d \in Disk :
      \E s \in 1..N :
        \E dst \in 1..N :
          /\ s # dst
          /\ IsSmallest(d, towers[s])
          /\ NoSmaller(d, towers[dst])
          /\ towers' = [towers EXCEPT 
                         ![s]   = towers[s] - d,
                         ![dst] = towers[dst] + d]

Next == Move

Init == 
    towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]

\* Type correctness: each tower holds a natural less than 2^D
TypeOK == 
    /\ towers \in [1..N -> Nat]
    /\ \A i \in 1..N : towers[i] < 2 ^ D

\* Conservation invariant: total of all tower values equals 2^D - 1
Inv == (\Sum i \in 1..N : towers[i]) = (2 ^ D) - 1

vars == <<towers>>

Spec == Init /\ [][Next]_vars

====