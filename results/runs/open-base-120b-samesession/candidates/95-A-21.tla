---- MODULE GameOfLife ----
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANT N

(*--------------------------------------------------------------------
  Positions on the N-by-N grid
--------------------------------------------------------------------*)
Pos == 1 .. N
Positions == Pos \X Pos

(*--------------------------------------------------------------------
  Offsets of the eight neighboring cells
--------------------------------------------------------------------*)
NeighborOffsets == {
    <<-1, -1>>, <<-1,  0>>, <<-1,  1>>,
    << 0, -1>>,               << 0,  1>>,
    << 1, -1>>, << 1,  0>>, << 1,  1>>
}

(*--------------------------------------------------------------------
  Helper: number of live neighbors of a position p
--------------------------------------------------------------------*)
NeighborCount(p) ==
  LET r == p[1] IN
  LET c == p[2] IN
    Sum({ 
        IF (r + o[1] \in Pos) /\ (c + o[2] \in Pos)
           THEN IF grid[r + o[1], c + o[2]] THEN 1 ELSE 0
           ELSE 0
        : o \in NeighborOffsets })

VARIABLES grid

(*--------------------------------------------------------------------
  Invariant: grid is a total mapping from Positions to BOOLEAN
--------------------------------------------------------------------*)
TypeOK == grid \in [Positions -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state: any Boolean assignment to the grid
--------------------------------------------------------------------*)
Init ==
  /\ TypeOK
  /\ grid \in [Positions -> BOOLEAN]

(*--------------------------------------------------------------------
  Next-state relation: simultaneous Game of Life update
--------------------------------------------------------------------*)
Next ==
  /\ TypeOK
  /\ grid' = [p \in Positions |-> 
        LET n == NeighborCount(p) IN
          IF grid[p] 
             THEN (n = 2) \/ (n = 3)
             ELSE (n = 3)
      ]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<grid>>

====