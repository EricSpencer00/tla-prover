---- MODULE Hanoi ----
EXTENDS Naturals

CONSTANTS D, N

Split == N - 1

\* tower[k] = sum of the size values of the disks currently resting on
\* tower k; the size values are distinct powers of two, so the binary
\* representation of tower[k] is the set of disks on that tower.
VARIABLES tower

vars == <<tower>>

TypeOK == /\ tower \in [0 .. Split -> 0 .. (2 ^ D) - 1]
          /\ \A a \in 0 .. Split : tower[a] >= 0

Init == /\ tower[0] = (2 ^ D) - 1
        /\ \A a \in 1 .. Split : tower[a] = 0

\* The amount a disk occupies in a tower value is the disk's size, which
\* is a power of two.  Precondition (2) above is what makes the power-of-two
\* encoding a proper ordering: a disk is movable only if no smaller disk is
\* present on the same tower (no lower-order bit is set).
Move(d, src, dst) == /\ d \in { 1 << k : k \in 0 .. (D - 1) }
                     /\ src # dst
                     /\ (tower[src] /\ d) = d
                     /\ (tower[src] % d) = 0
                     /\ (tower[dst] = 0 \/ (tower[dst] % d) = 0)
                     /\ tower' = [tower EXCEPT ![src] = @ - d, ![dst] = @ + d]

Next == \E d \in { 1 << k : k \in 0 .. (D - 1) } : \E src \in 0 .. Split :
          \E dst \in 0 .. Split : Move(d, src, dst)

Spec == Init /\ [][Next]_vars

\* Conservation: the number of disks never changes.
Inv == (tower[0] + tower[1] + IF N > 2 THEN tower[2] ELSE 0) = (2 ^ D) - 1

====