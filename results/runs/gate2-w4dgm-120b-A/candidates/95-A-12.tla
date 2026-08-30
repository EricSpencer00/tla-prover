---- MODULE GameOfLife ----
EXTENDS Integers

CONSTANTS N

\* A grid position is a pair of 1..N indices; positions outside the grid are
\* treated as dead when counting neighbors (boundary condition).
Pos == 0..N+1

VARIABLES cells

vars == <<cells>>

Grid == {1..N} \X {1..N}

Neighbors == {1, 2, 3, 4, 5, 6, 7, 8}

\* Off-grid coordinates (0 or N+1) return FALSE = dead.
CellAlive(r, c) == IF <<r, c>> \in Grid THEN cells[<<r, c>>] ELSE FALSE

LiveNeighbors(r, c) ==
  Cardinality({n \in Neighbors :
    LET dr == CASE n = 1 -> -1 [] n = 2 -> -1 [] n \in {3, 5} -> 0 [] OTHER -> 1
        dc == CASE n \in {1, 3, 7} -> -1 [] n \in {2, 6} -> 0 [] OTHER -> 1
    IN CellAlive(r + dr, c + dc)})

TypeOK == cells \in [Grid -> BOOLEAN]

\* The initial grid is nondeterministic: any alive/dead pattern is possible.
Init == cells \in [Grid -> BOOLEAN]

\* Simultaneous update: the next generation is computed once from the current
\* generation, not in-place, so the rule is applied to every cell at once.
Tick == cells' = [p \in Grid |->
    LET r == p[1] c == p[2]
        ln == LiveNeighbors(r, c)
        alive == cells[p]
    IN (alive /\ ln \in {2, 3}) \/ (~alive /\ ln = 3)]

Next == Tick

Spec == Init /\ [][Next]_vars

\* Nothing more than a type check is needed: each cell simply stays a boolean.
TypeOKInv == TypeOK

====