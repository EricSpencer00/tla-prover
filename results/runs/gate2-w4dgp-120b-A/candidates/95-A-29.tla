---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

Cells == {1 .. N} \X {1 .. N}
Neighbors == {{-1, -1}, {-1, 0}, {-1, 1}, {0, -1}, {0, 1}, {1, -1}, {1, 0}, {1, 1}}

VARIABLES alive

TypeOK == alive \in [{1 .. N} \X {1 .. N} -> BOOLEAN]

\* One time step: the entire grid updates simultaneously.  A cell is alive in
\* the next generation iff it is currently alive with 2 or 3 live neighbors,
\* or it is currently dead with exactly 3 live neighbors.
Tick ==
    /\ LET lcount(p) ==
           LET neighbors ==
               {<<r + dr, c + dc>> : <<dr, dc>> \in Neighbors}
               \ {p}
           IN Cardinality({q \in (neighbors \cap Cells) : alive[q]})
       IN
           alive' = {[p \in Cells |-> (alive[p] /\ (lcount(p) = 2 \/ lcount(p) = 3))
                                  \/ (~alive[p] /\ lcount(p) = 3)])}

Next == Tick

Init ==
    /\ alive \in [Cells -> BOOLEAN]

Spec == Init /\ [][Next]_alive

====