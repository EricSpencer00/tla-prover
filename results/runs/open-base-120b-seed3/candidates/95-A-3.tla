---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLES grid

(* ---------------------------------------------------------------------- *)
(* The set of all positions on the N×N grid *)
Cell == (1 .. N) \X (1 .. N)

(* ---------------------------------------------------------------------- *)
Abs(x) == IF x >= 0 THEN x ELSE -x

Row(p) == p[1]
Col(p) == p[2]

(* ---------------------------------------------------------------------- *)
Neighbors(p) ==
    { q \in Cell :
        q # p /\                     \* different position
        Abs(Row(q) - Row(p)) <= 1 /\ 
        Abs(Col(q) - Col(p)) <= 1 }

AliveNeighbors(p) ==
    Cardinality({ q \in Neighbors(p) : grid[q] })

(* ---------------------------------------------------------------------- *)
Tick ==
    /\ \A p \in Cell :
        LET n == AliveNeighbors(p) IN
        grid'[p] = (grid[p] /\ (n = 2 \/ n = 3)) \/ (~grid[p] /\ n = 3)

Next == Tick

(* ---------------------------------------------------------------------- *)
Init == grid \in [Cell -> BOOLEAN]

TypeOK == grid \in [Cell -> BOOLEAN]

Spec == Init /\ [][Next]_grid

====