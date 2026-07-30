---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

\* The set of positions on the grid, each holding a cell that is either alive or dead.
Cells == 1..N \X 1..N

\* Cell(x) is the boolean state of the cell at grid position x (true = alive, false = dead).
VARIABLES Cell

TypeOK == Cell \in [Cells -> BOOLEAN]

Init == Cell = [x \in Cells |-> CHOOSE b \in BOOLEAN : TRUE]

\* Neighbors(x) are the positions adjacent horizontally, vertically, or diagonally to x
\* that fall inside the grid; positions outside the grid are omitted here and treated
\* as dead by construction, which is exactly what "outside cells are dead" means.
Neighbors(x) == { y \in Cells : y # x /\ Cardinality({i \in {1,2} : x[i] - y[i] \in {-1,0,1}}) = 2 }

LiveNeighbors(x) == Cardinality({ y \in Neighbors(x) : Cell[y] })

Tick == Cell' = [x \in Cells |->
                    IF Cell[x] /\ (LiveNeighbors(x) = 2 \/ LiveNeighbors(x) = 3)
                    THEN TRUE
                    ELSE IF ~Cell[x] /\ LiveNeighbors(x) = 3
                    THEN TRUE
                    ELSE FALSE ]

Next == Tick

\* With a nondeterministic initial configuration but a deterministic update rule, each
\* reachable state is uniquely determined by its predecessor (the TLC state graph is a
\* tree branching only at Init and converging thereafter).
Spec == Init /\ [][Next]_Cell

====