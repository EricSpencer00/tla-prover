---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == towers

\* Tower values are interpreted as bitsets: tower v has exactly the disks
\* whose sizes sum to v, and each disk size is a distinct power of two.
\* Conservation is equality of the *sum of tower values* with the full set.
RECURSIVE SumF(_)
SumF(S) == IF S = {} THEN 0
           ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumF(S \ {x})

TypeOK ==
    /\ towers \in [1..N -> 0..(2^D - 1)]
    /\ SumF(1..N) = 2^D - 1

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

Move(disk, src, dst) ==
    /\ src # dst
    /\ (towers[src] >= disk)
    /\ (towers[src] % (2 * disk) = disk)
    /\ (towers[dst] % (2 * disk) = 0)
    /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
    \E disk \in { 2^k : k \in 0..(D - 1) } :
        \E src \in 1..N :
            \E dst \in 1..N :
                Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

Inv == SumF(1..N) = 2^D - 1

====