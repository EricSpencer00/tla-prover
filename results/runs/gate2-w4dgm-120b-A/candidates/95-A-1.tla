---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES alive

vars == <<alive>>

Cells == 1..N

Neighbors == [x : Cells, y : Cells]

WithinGrid(c) == c.x \in Cells /\ c.y \in Cells

\* Neighbor count uses the current alive mapping only; cells outside the grid
\* are treated as dead (zero contribution) rather than excluded from a set.
CountAlive(c) ==
  Cardinality({n \in Neighbors : WithinGrid(n) /\ n # c /\ alive[n.x, n.y]})

TypeOK ==
  /\ alive \in [Cells \X Cells -> BOOLEAN]

Init ==
  \E a \in [Cells \X Cells -> BOOLEAN] : alive = a

\* Global synchronous update: the new grid is computed entirely from the old
\* one and then replaces it in a single step.
Tick ==
  /\ LET na ==
       [p \in Cells \X Cells |->
          IF alive[p] /\ (CountAlive(p) = 2 \/ CountAlive(p) = 3) \/ (~alive[p] /\ CountAlive(p) = 3)
          THEN TRUE ELSE FALSE]
     IN alive' = na
  /\ UNCHANGED <<>>

Next == Tick

Spec == Init /\ [][Next]_vars

====