---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

TowerIndices == 0..(N - 1)

Bits(k) == 2 ^ k

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET k == CHOOSE e \in S : TRUE IN Bits(k) + SumOf(S \ {k})

RECURSIVE SumTowers(_)
SumTowers(f, S) ==
    IF S = {} THEN 0
    ELSE LET i == CHOOSE e \in S : TRUE IN f[i] + SumTowers(f, S \ {i})

VARIABLES towers

vars == <<towers>>

Goal == [i \in TowerIndices |-> IF i = N - 1 THEN SumOf(TowerIndices) ELSE 0]

Init ==
    /\ towers = [i \in TowerIndices |-> IF i = 0 THEN SumOf(TowerIndices) ELSE 0]
    /\ UNCHANGED << >>

Move(disk, src, dst) ==
    /\ src # dst
    /\ towers[src] >= disk
    /\ (towers[src] % (2 * disk)) >= disk
    /\ (IF towers[dst] = 0 THEN TRUE ELSE (towers[dst] % (2 * disk)) < disk)
    /\ towers' = [towers EXCEPT ![src] = towers[src] - disk, ![dst] = towers[dst] + disk]
    /\ UNCHANGED << >>

Next ==
    \/ \E src, dst \in TowerIndices : Move(Bits(0), src, dst)
    \/ \E src \in TowerIndices, dst \in TowerIndices : Move(Bits(1), src, dst)
    \/ \E src \in TowerIndices, dst \in TowerIndices : Move(Bits(2), src, dst)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == \A i \in TowerIndices : towers[i] \in 0..(SumOf(TowerIndices))

Inv == SumTowers(towers, TowerIndices) = SumOf(TowerIndices)

====