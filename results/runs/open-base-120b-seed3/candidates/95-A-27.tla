---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

VARIABLE grid

(* ----------------------------------------------------------------------
   Definitions
   ---------------------------------------------------------------------- *)

Pos == { <<i, j>> : i \in 1..N /\ j \in 1..N }

Abs(x) == IF x >= 0 THEN x ELSE -x

Neighbors(p) == 
    { q \in Pos :
        q # p /\ 
        Abs(q[1] - p[1]) <= 1 /\ 
        Abs(q[2] - p[2]) <= 1 }

CountNeighbors(p, g) == 
    Cardinality({ q \in Neighbors(p) : g[q] })

Next == 
    /\ \A p \in Pos :
          LET n == CountNeighbors(p, grid) IN
          grid'[p] = ( grid[p] /\ (n = 2 \/ n = 3) ) \/ ( ~grid[p] /\ n = 3 )
    /\ UNCHANGED << >>

Init == 
    /\ grid \in [Pos -> BOOLEAN]   \* nondeterministic assignment

Spec == Init /\ [][Next]_<<grid>>

TypeOK == grid \in [Pos -> BOOLEAN]

=============================================================================