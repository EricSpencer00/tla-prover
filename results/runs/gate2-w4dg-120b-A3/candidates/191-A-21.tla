---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Tower states are encoded as bitwise sums of disk values. Each disk's size is
\* a distinct power of two, so the binary representation of a tower's value
\* carries exactly which disks sit on it.
Disks == { 2 ^ k : k \in 0..(D - 1) }
EmptyTowers == { i \in 0..(N - 1) : i # 0 /\ i # (N - 1) }
Total == (2 ^ D) - 1
BitwiseAnd(x, y) == x - ((x + y) % (2 ^ D))

VARIABLES towers
vars == <<towers>>

TypeOK ==
    /\ towers \in [0..(N - 1) -> 0..Total]

Init ==
    /\ towers[0] = Total
    /\ \A i \in EmptyTowers : towers[i] = 0

\* A move is valid iff the disk is present on the source tower, is the smallest
\* disk there, and finds no smaller disk on the destination tower.
ValidMove(d, src, dst) ==
    /\ src # dst
    /\ towers[src] >= d
    /\ BitwiseAnd(towers[src], d - 1) = 0
    /\ BitwiseAnd(towers[dst], d - 1) = 0

Move(d, src, dst) ==
    /\ ValidMove(d, src, dst)
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \/ \E d \in Disks, src \in 0..(N - 1), dst \in 0..(N - 1) : Move(d, src, dst)

\* The conservation law: the bitwise sum of all towers always accounts for every
\* disk exactly once, so no move ever creates or destroys a disk.
Conservation ==
    LET f[S \in SUBSET (0..(N - 1))] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN towers[x] + f[S \ {x}]
    IN f[0..(N - 1)] = Total

Spec == Init /\ [][Next]_vars

Inv == Conjunction({ TypeOK, Conservation })
====