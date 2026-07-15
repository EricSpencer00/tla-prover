---- MODULE GameOfLife ----
EXTENDS Naturals, Sequences, TLC

CONSTANT N \* grid dimension, to be supplied in the .cfg

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES grid

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Cell == 1..N
Pos  == [i \in Cell, j \in Cell]

Alive == TRUE
Dead  == FALSE

Neighbors(p) ==
  { [i \in Cell, j \in Cell] :
        i \in 1..N /\ j \in 1..N /\ 
        i # p["i"] \/ j # p["j"] /\ 
        Abs(i - p["i"]) <= 1 /\ Abs(j - p["j"]) <= 1 }

LiveNeighbors(g, p) ==
  Cardinality({ q \in Neighbors(p) : g[q] = Alive })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ grid \in [Pos -> BOOLEAN]
  /\ \A p \in Pos: grid[p] \in {Alive, Dead}
  /\ \A p \in Pos:
        IF RANDOM() < 0.5 THEN grid[p] = Alive
        ELSE grid[p] = Dead

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
  /\ grid' = [p \in Pos |-> 
        LET n == LiveNeighbors(grid, p) IN
          IF grid[p] = Alive THEN (n = 2) \/ (n = 3)
          ELSE n = 3]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Tick]_<<grid>>

\* ----------------------------------------------------------------------
\* Type invariant (ensures grid maps each position to a Boolean)
\* ----------------------------------------------------------------------
TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================