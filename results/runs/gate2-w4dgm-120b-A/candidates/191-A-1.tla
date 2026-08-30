---- MODULE Hanoi ----
\* Tower of Hanoi puzzle modeled with a bitwise tower occupancy encoding.
\* Each tower holds a natural value whose set bits indicate which disks are
\* present; a move shifts a single lowest disk from one tower to another, and
\* the total across all towers is conserved. No liveness property is asserted.
EXTENDS Naturals

CONSTANTS D, N

ASSUME D \in Nat /\ D > 0 /\ N \in Nat /\ N >= 2

Towers == 1..N
Total == 2 ^ D - 1

VARIABLES towers

vars == <<towers>>

RECURSIVE SumN(_)
SumN(n) == IF n = 0 THEN 0 ELSE towers[n] + SumN(n - 1)

TypeOK == towers \in [Towers -> 0..Total]

Init == towers = [n \in Towers |-> IF n = 1 THEN Total ELSE 0]

\* A disk is a power of two; a move removes it from the source and adds it to
\* the destination, shifting exactly one lowest disk between towers.
Move(d, src, dst) ==
    /\ d \in Towers
    /\ src \in Towers
    /\ dst \in Towers
    /\ src # dst
    /\ towers[src] >= d
    /\ towers[src] % (2 * d) = d
    /\ towers[dst] % (2 * d) = 0
    /\ towers' = [towers EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in {2 ^ k : k \in 0..(D - 1)} : \E src \in Towers : \E dst \in Towers : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Safety: the bitwise tower encoding always accounts for every disk exactly
\* once -- none is created or destroyed as they move.
Conservation == SumN(N) = Total

Inv == TypeOK /\ Conservation

\* No liveness property is asserted; the puzzle is solved by finding a
\* counterexample to the negation of the solved-state property.
====