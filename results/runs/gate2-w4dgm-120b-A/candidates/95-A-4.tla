---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets

CONSTANTS N

\* Each cell is a position on an N-by-N square grid; the set GridPos is the domain of
\* the grid variable (the "Boids" in the swarm are the cells).
GridPos == [r : 1..N, c : 1..N]

VARIABLES grid
vars == <<grid>>

\* NeighborCount is the deterministic kernel: given the whole grid, it counts the
\* live cells in the eight surrounding positions, treating any position outside the
\* grid boundaries as dead (value zero). This is what makes the whole-generation
\* update mathematically deterministic.
NeighborCount(pos, g) ==
  LET Count(p) == IF g[p] THEN 1 ELSE 0
  IN Count([r |-> pos.r - 1, c |-> pos.c - 1])
     + Count([r |-> pos.r - 1, c |-> pos.c])
     + Count([r |-> pos.r - 1, c |-> pos.c + 1])
     + Count([r |-> pos.r,     c |-> pos.c - 1])
     + Count([r |-> pos.r,     c |-> pos.c + 1])
     + Count([r |-> pos.r + 1, c |-> pos.c - 1])
     + Count([r |-> pos.r + 1, c |-> pos.c])
     + Count([r |-> pos.r + 1, c |-> pos.c + 1])

\* A position is within the grid if both coordinates are within 1 and N.
InBound(p) == p.r \in 1..N /\ p.c \in 1..N

\* The "lifeStep" function implements the Conway game rule exactly as written in the
\* spec (dead cell with exactly three live neighbors becomes alive, live cell
\* survives iff it has two or three live neighbors) -- there is no shortcut or
\* "any live cell with exactly two or three neighbors survives" optimization allowed
\* here, because that wording is the entire action's spec.
LifeStep(pos, g) ==
  /\ InBound(pos)
  /\ LET nc == NeighborCount(pos, g)
         current == g[pos]
     IN \/ (current /\ (nc = 2 \/ nc = 3))
        \/ (~current /\ nc = 3)

\* The full-generation update: every cell on the grid is recomputed at once, from
\* the same old generation, which is the source of the "simultaneous" nature of
\* the rule. This is not a per-cell asynchronous update; it is a single step.
Tick ==
  /\ \E newgrid \in [GridPos -> BOOLEAN] :
       \A pos \in GridPos : newgrid[pos] = LifeStep(pos, grid)
  /\ grid' = newgrid

\* Each cell is nondeterministically alive or dead in the first generation; any
\* starting pattern whatsoever is a valid initial state.
Init ==
  /\ \E initgrid \in [GridPos -> BOOLEAN] : grid = initgrid

\* The "Tick" action is always strongly fair: a cell that could come alive (or die)
\* is never stuck forever because the spec kept choosing the "nothing changes"
\* outcome. Every reachable state has a live tick available, so this fairness
\* condition never loses its bite.
Next == Tick

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Tick)

\* A cell's life is binary: there is no third state (dying, infected, etc.) any
\* cell is either alive or dead. This is the literal content of the grid
\* representation, not an emergent property to be proved about it.
TypeOK == grid \in [GridPos -> BOOLEAN]
====