---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN (2 ^ D) - 1 ELSE 0]
    /\ TRUE

\* Remove the smallest set bit from v, returning that bit's value (zero if none).
SmallestSetBit(v) ==
    IF v = 0 THEN 0
    ELSE 2 ^ (CHOOSE k \in 0..(D - 1) : ((v \ DIV  (2 ^ k)) % 2) = 1)

\* True iff the D-bit pattern of v is contiguous ones from the LSB up to its MSB.
ContiguousOnes(v) ==
    \/ v = 0
    \/ \E k \in 1..D : v = (2 ^ k) - 1

Move ==
    /\ \E i, j \in 1..N :
        /\ i # j
        /\ towers[i] # 0
        /\ towers[j] # (2 ^ D) - 1
        /\ LET d == SmallestSetBit(towers[i]) IN
            /\ d # 0
            /\ ContiguousOnes(d - 1)
            /\ ContiguousOnes(towers[j])
            /\ towers' = [towers EXCEPT ![i] = @ - d, ![j] = @ + d]
    /\ TRUE

Next == Move

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ towers \in [1..N -> 0..((2 ^ D) - 1)]
    /\ \A i \in 1..N : towers[i] >= 0

\* Conservation: the disks are only ever moved between towers, so their summed
\* value is invariant; no disk is created or destroyed.
Inv ==
    /\ (towers[1] + towers[2] + towers[3]) = ((2 ^ D) - 1)
    /\ towers[1] >= 0
    /\ towers[2] >= 0
    /\ towers[3] >= 0

====