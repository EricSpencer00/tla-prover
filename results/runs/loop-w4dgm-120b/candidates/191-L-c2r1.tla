---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

\* Disk sizes are powers of two: 1, 2, 4, ..., 2^(D-1). A tower's value is the
\* sum of the sizes of the disks on it, so the binary representation of a
\* tower value encodes exactly which disks that tower holds.
VARIABLES tower, moves

vars == <<tower, moves>>

Towers == 0..(N - 1)
Disks == { 2 ^ k : k \in 0..(D - 1) }

RECURSIVE SumTowers(_)
SumTowers(S) ==
    IF S = {} THEN 0
    ELSE LET t == CHOOSE x \in S : TRUE IN tower[t] + SumTowers(S \ {t})

OnTower(d, t) == (tower[t] \div d) % 2 = 1

TopDisk(t) ==
    IF \E d \in Disks : OnTower(d, t) /\ \A e \in Disks : OnTower(e, t) => e >= d
    THEN CHOOSE d \in Disks :
            OnTower(d, t) /\ \A e \in Disks : OnTower(e, t) => e >= d
    ELSE 0

TypeOK ==
    /\ tower \in [Towers -> 0..(2 ^ D - 1)]
    /\ moves \in 0..7

Init ==
    /\ tower = [t \in Towers |-> IF t = 0 THEN 2 ^ D - 1 ELSE 0]
    /\ moves = 0

Move(d, from, to) ==
    /\ moves < 7
    /\ from # to
    /\ OnTower(d, from)
    /\ TopDisk(from) = d
    /\ (tower[to] = 0 \/ TopDisk(to) > d)
    /\ tower' = [tower EXCEPT ![from] = @ - d, ![to] = @ + d]
    /\ moves' = moves + 1

Next ==
    \E d \in Disks, from \in Towers, to \in Towers : Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Conservation: the tower encoding loses no disk and creates no disk.
Inv == SumTowers(Towers) = 2 ^ D - 1
====