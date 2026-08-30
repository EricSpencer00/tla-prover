---- MODULE Hanoi ----
EXTENDS Integers

CONSTANTS D, N

\* Tower k's value is a bitfield: bit i set <=> disk 2^i sits on tower k.
\* Conservation is literally sum of tower values = (2^D) - 1.
VARIABLES towers

vars == <<towers>>

Disk(d) == 1 << d

TypeOK ==
    /\ towers \in [0..(N - 1) -> 0..(2 ^ D) - 1]
    /\ \A k \in 0..(N - 1): towers[k] >= 0 /\ towers[k] < 2 ^ D

Init ==
    /\ towers = [k \in 0..(N - 1) |-> IF k = 0 THEN 2 ^ D - 1 ELSE 0]

\* d-th disk is present on k iff its bit is set in towers[k].
\* A valid move removes the smallest disk from the source and puts it on the dest.
Move ==
    /\ \E d \in 0..(D - 1), src \in 0..(N - 1), dest \in 0..(N - 1):
         /\ src # dest
         /\ towers[src] >= Disk(d)
         /\ (towers[src] % Disk(d + 1)) = Disk(d)
         /\ towers[dest] % Disk(d + 1) = 0
         /\ towers' = [towers EXCEPT ![src] = @ - Disk(d), ![dest] = @ + Disk(d)]
    /\ UNCHANGED << >>

\* Conservation: the bitwise representation moves disks, never invents or loses them.
Conservation ==
    LET Sum[S \in SUBSET (0..(N - 1))] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN towers[x] + Sum[S \ {x}]
    IN Sum[0..(N - 1)] = 2 ^ D - 1

Spec == Init /\ [][Move]_vars

Inv == TypeOK /\ Conservation

\* The full solution is not a liveness property; the checker searches for a
\* Counterexample to the negated goal: all disks on the last tower.
Goal == towers[N - 1] = 2 ^ D - 1

====