---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE Grid

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

Pos == 1..N
CellPos == Pos \X Pos

(* Type invariant *)
TypeOK == Grid \in [CellPos -> BOOLEAN]

(* Neighbor positions of (i,j) within the grid, excluding (i,j) itself *)
Neighbors(i, j) ==
  { <<p, q>> \in CellPos :
      (p # i \/ q # j) /\               \* not the cell itself
      p \in (i - 1) .. (i + 1) /\ 
      q \in (j - 1) .. (j + 1) }

(* Number of live neighbours of cell (i,j) in grid g *)
NeighborCount(g, i, j) ==
  Cardinality({ <<p, q>> \in Neighbors(i, j) : g[<<p, q>>] })

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)

Init ==
  /\ TypeOK               \* any assignment of true/false to all cells

(*--------------------------------------------------------------------
  Transition (Tick)
--------------------------------------------------------------------*)

Next ==
  LET NewGrid ==
        [pos \in CellPos |-> 
           LET i == pos[1] IN
           LET j == pos[2] IN
           LET cnt == NeighborCount(Grid, i, j) IN
             IF Grid[pos] 
               THEN (cnt = 2) \/ (cnt = 3)   \* survival
               ELSE (cnt = 3)                \* birth
        ]
  IN
    /\ Grid' = NewGrid
    /\ UNCHANGED << >>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<Grid>>

====