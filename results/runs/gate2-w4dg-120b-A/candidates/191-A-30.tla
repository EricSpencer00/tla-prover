---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS
    D, \* number of disks (each of a unique size, encoded as a power of two)
    N  \* number of towers (pegs)

\* Tower values encode which disks are present, via their binary bits:
\* bit k set <=> the disk of size 2^k is on that tower.
Towers == 1..N
Disk(i) == 2 ^ i

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOf(S \ {x})

VARIABLES tower

vars == <<tower>>

TypeOK ==
    /\ tower \in [Towers -> 0..(2 ^ D - 1)]

Init ==
    /\ tower = [t \in Towers |-> IF t = 1 THEN 2 ^ D - 1 ELSE 0]

\* Valid move: the disk is present, is the smallest on its source tower,
\* and the destination tower has no smaller disk (or is empty).
Move(d, src, dst) ==
    /\ d \in {Disk(i) : i \in 0..(D - 1)}
    /\ src # dst
    /\ tower[src] >= d
    /\ (tower[src] % (2 * d)) = d
    /\ (tower[dst] % (2 * d)) = 0
    /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]
    /\ UNCHANGED << >>

Next ==
    \/ \E d \in {Disk(i) : i \in 0..(D - 1)}, src \in Towers, dst \in Towers : Move(d, src, dst)

\* Conservation: the total disk value across all towers never changes.
Inv == SumOf({tower[t] : t \in Towers}) = 2 ^ D - 1

Spec == Init /\ [][Next]_vars

====