---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANT D, N

\* Each tower's value is a bitwise encoding: bit k set means the disk of size 2^k
\* sits on that tower. Conservation of disk mass is then conservation of the
\* summed tower values, since each disk contributes exactly its own value.
VARIABLES towers

vars == <<towers>>

Disk(k) == 2 ^ k

Init ==
    /\ towers = [i \in 1..N |-> IF i = 1 THEN 2 ^ D - 1 ELSE 0]
    /\ UNCHANGED towers

Move(d, src, dst) ==
    /\ d >= 1 /\ d < 2 ^ D /\ d * 2 <= 2 ^ D
    /\ src # dst
    /\ (towers[src] / d) % 2 = 1
    /\ towers[src] % (2 * d) = d
    /\ towers[dst] % (2 * d) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next ==
    \E d \in 1..(2 ^ D - 1), src, dst \in 1..N : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ towers \in [1..N -> 0..(2 ^ D - 1)]
    /\ D \in Nat /\ N \in Nat

Inv ==
    /\ (\A i \in 1..N : towers[i] \in Nat)
    /\ (LHS == 2 ^ D - 1)
    /\ LHS = towers[1] + towers[2] + towers[3]

LHS == towers[1] + towers[2] + towers[3]

====