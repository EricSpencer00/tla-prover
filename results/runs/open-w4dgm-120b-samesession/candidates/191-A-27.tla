---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [0 .. N - 1 -> 0 .. (2 ^ D) - 1]
          /\ \A i \in 0 .. N - 1 : tower[i] >= 0

\* Conservation: the total physical quantity encoded across all towers is
\* invariant -- the bitwise-encoded disks are neither created nor destroyed.
Conservation == (tower[0] + tower[1] + tower[2]) = (2 ^ D) - 1

Init == /\ tower = [i \in 0 .. N - 1 |-> IF i = 0 THEN (2 ^ D) - 1 ELSE 0]
        /\ UNCHANGED tower

\* A move isolates a single disk (a power of two) and relocates it, which means
\* in the encoding: clear its value from the source and add it to the
\* destination. The move is guarded by the smallest-on-tower rule, expressed
\* in terms of the bits set below the candidate disk.
Move(d, src, dst) ==
    /\ d >= 1 /\ d <= (2 ^ D - 1) /\ (d * 2) \notin (1 .. (2 ^ D - 1))
    /\ src # dst
    /\ (tower[src] \in [1 .. (2 ^ D) - 1] /\ (tower[src] \ div d) % 2 = 1)
    /\ (tower[src] % d = 0)
    /\ (tower[dst] % d = 0)
    /\ tower' = [tower EXCEPT ![src] = tower[src] - d, ![dst] = tower[dst] + d]

Next == \E d \in 1 .. (2 ^ D) - 1, src \in 0 .. N - 1, dst \in 0 .. N - 1 : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

Inv == Conservation

====