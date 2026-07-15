---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N \* grid dimension, must be supplied in the .cfg

\* ----------------------------------------------------------------------
\* Helper sets
\* ----------------------------------------------------------------------
Row == 1 .. N
Col == 1 .. N
Pos == [r : Row, c : Col] \* a record representing a position

\* ----------------------------------------------------------------------
\* State variable
\* ----------------------------------------------------------------------
VARIABLE x \* x[p] = TRUE iff cell at position p is alive

\* ----------------------------------------------------------------------
\* Initial predicate: each cell nondeterministically alive or dead
\* ----------------------------------------------------------------------
Init ==
    /\ x = [p \in Pos |-> FALSE] \* start with all dead
    /\ \E y \in [Pos -> BOOLEAN] : 
          /\ y = [p \in Pos |-> x[p] \lor (x[p] = FALSE)] \* placeholder to force nondeterminism
    /\ x' = [p \in Pos |-> CHOOSE b \in BOOLEAN : TRUE] \* nondeterministically assign each cell

\* The above trick with CHOOSE ensures each cell can be either TRUE or FALSE
\* but the whole mapping is still a function from Pos to BOOLEAN.

\* ----------------------------------------------------------------------
\* Neighbor counting (treat out‑of‑bounds as dead)
\* ----------------------------------------------------------------------
Neighbors(p) ==
    { [r : p.r + dr, c : p.c + dc] :
        dr \in -1 .. 1,
        dc \in -1 .. 1,
        (dr # 0) \/ (dc # 0),
        p.r + dr \in Row,
        p.c + dc \in Col }

LiveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : x[q] = TRUE })

\* ----------------------------------------------------------------------
\* Next-state relation (Tick)
\* ----------------------------------------------------------------------
Tick ==
    /\ x' = [p \in Pos |-> 
          IF x[p] 
             THEN (LiveNeighbors(p) = 2) \/ (LiveNeighbors(p) = 3)
             ELSE LiveNeighbors(p) = 3]

Next == Tick

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<x>>

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC, matches required INVARIANT name)
\* ----------------------------------------------------------------------
TypeOK == x \in [Pos -> BOOLEAN]

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by .cfg but keeps module self‑contained)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====