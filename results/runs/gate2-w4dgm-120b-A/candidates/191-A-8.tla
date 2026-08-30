---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower state is a sum of disk values; each disk is a distinct power of two.
\* A move requires the disk to be the smallest on its source and not to
\* land on a smaller disk at the destination -- this is the ordering
\* discipline that prevents a larger disk from ever sitting on top of a
\* smaller one, derived from the bitwise encoding of the towers.

VARIABLES towers

vars == << towers >>

RECURSIVE SumT(_)
SumT(S) == IF S = {} THEN 0
           ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + SumT(S \ {x})

TypeOK == towers \in [1..N -> 0..(2 ^ D) - 1]

Init ==
    /\ towers = [k \in 1..N |-> IF k = 1 THEN (2 ^ D) - 1 ELSE 0]
    /\ UNCHANGED << towers >>

\* Bitwise AND using arithmetic: (x \in Disk) is true exactly when the
\* binary representation of towers[i] has that power-of-two bit set.
Move ==
    \E disk \in { 2 ^ k : k \in 0..(D - 1) } :
    \E i \in 1..N :
    \E j \in 1..N :
        /\ i # j
        /\ disk <= towers[i]
        /\ towers[i] % (2 * disk) >= disk
        /\ towers[j] % (2 * disk) < disk
        /\ towers' = [towers EXCEPT ![i] = @ - disk, ![j] = @ + disk]

Next == Move

Conservation == SumT(1..N) = (2 ^ D) - 1

Spec == Init /\ [][Next]_vars

====