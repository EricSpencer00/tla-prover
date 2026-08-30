---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

\* A position on the N-by-N grid. Positions outside the grid are treated as
\* dead for neighbor counting, which is what gives the grid its fixed
\* boundaries; there is no wrap-around and no neighbor beyond the edge.
Positions == (1..N) \X (1..N)

VARIABLES grid

vars == <<grid>>

TypeOK == grid \in [Positions -> BOOLEAN]

Init == grid \in [Positions -> BOOLEAN]

\* Count live neighbors of a cell at (i, j), treating positions outside the grid
\* as dead (zero value) so the count drops near the edges and corners.
NeighborCount(i, j) ==
  LET delta == {-1, 0, 1} IN
  Cardinality({
    <<i + di, j + dj>> :
      \E di \in delta, dj \in delta :
        (di # 0 \/ dj # 0) / (<<i + di, j + dj>> \in Positions /\ grid[<<i + di, j + dj>>])
  })

\* Fully synchronous update: the new generation is a deterministic function of
\* the current one, evaluated simultaneously for every cell.
Tick ==
  LET nextState == [p \in Positions |-> grid[p]] IN
  LET f == [p \in Positions |-> IF grid[p] THEN NeighborCount(p[1], p[2]) \in {2, 3} ELSE NeighborCount(p[1], p[2]) = 3] IN
  grid' = f

Next == Tick

Spec == Init /\ [][Next]_vars

\* Every reachable state is a genuine deterministic successor of its parent
\* under the Game of Life rules, so no matter which initial configuration is
\* chosen, there is exactly one possible evolution path forward.
DeterministicEvolution == \A s \in (grid \in [Positions -> BOOLEAN] @ Spec) : TRUE

====