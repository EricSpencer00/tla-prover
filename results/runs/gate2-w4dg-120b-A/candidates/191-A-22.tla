---- MODULE Hanoi ----
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

VARIABLES towers

vars == <<towers>>

Mask == 2 ^ D - 1
Disk(k) == 2 ^ k

Lowest(t) == t % 2

TypeOK ==
  /\ towers \in [1..N -> 0..Mask]
  /\ towers[1] = Mask

Init ==
  /\ towers = [i \in 1..N |-> IF i = 1 THEN Mask ELSE 0]

Move ==
  \E k \in 0..(D - 1), src \in 1..N, dst \in 1..N :
    /\ src # dst
    /\ (towers[src] \LAND Disk(k)) # 0
    /\ Lowest(towers[src]) = Disk(k)
    /\ (towers[dst] = 0 \/ Lowest(towers[dst]) > Disk(k))
    /\ towers' = [towers EXCEPT ![src] = @ - Disk(k), ![dst] = @ + Disk(k)]

Next == Move

Spec == Init /\ [][Next]_vars

Inv == \A t \in towers : t \in 0..Mask

====