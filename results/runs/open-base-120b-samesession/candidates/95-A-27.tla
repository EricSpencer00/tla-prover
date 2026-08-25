---- MODULE GameOfLife ----
EXTENDS Integers, Naturals, FiniteSets

CONSTANT N

(*--------------------------------------------------------------------
  Positions on the N-by-N grid
---------------------------------------------------------------------*)
Pos == 1..N \X 1..N

VARIABLES A

(*--------------------------------------------------------------------
  Type invariant: A is always a mapping from positions to BOOLEAN
---------------------------------------------------------------------*)
TypeOK == A \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state: any assignment of TRUE/FALSE to each cell
---------------------------------------------------------------------*)
Init == A \in [Pos -> BOOLEAN]

(*--------------------------------------------------------------------
  Neighbor relation (up to eight neighbors, staying inside the grid)
---------------------------------------------------------------------*)
Neighbors(p) ==
  { q \in Pos :
      q # p /\ 
      q[1] \in p[1] - 1 .. p[1] + 1 /\ 
      q[2] \in p[2] - 1 .. p[2] + 1 }

LiveCount(p) ==
  Cardinality({ q \in Neighbors(p) : A[q] })

(*--------------------------------------------------------------------
  One tick (simultaneous update of all cells)
---------------------------------------------------------------------*)
Next ==
  /\ A' = [p \in Pos |-> 
            LET n == LiveCount(p) IN
            IF A[p] THEN (n = 2 \/ n = 3) ELSE (n = 3) ]

(*--------------------------------------------------------------------
  Specification
---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_A
====