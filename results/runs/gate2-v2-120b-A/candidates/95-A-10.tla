---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

(* The set of all valid grid positions, defined as 1..N for both rows and columns *)
Pos == 1 .. N
Grid == Pos \X Pos

VARIABLE grid

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)

Neighbors(p) == 
  LET i == p[1] IN
  LET j == p[2] IN
  { <<i + di, j + dj>> : 
      di \in {-1, 0, 1} /\ 
      dj \in {-1, 0, 1} /\ 
      ~(di = 0 /\ dj = 0) /\ 
      i + di \in Pos /\ 
      j + dj \in Pos }

LiveNeighborsCount(p) == 
  Cardinality({ q \in Neighbors(p) : grid[q] })

WillBeAlive(p) == 
  IF grid[p] 
    THEN LiveNeighborsCount(p) \in {2, 3}
    ELSE LiveNeighborsCount(p) = 3

(*--------------------------------------------------------------------
  Type correctness invariant (required by the .cfg)
--------------------------------------------------------------------*)
TypeOK == grid \in [Grid -> BOOLEAN]

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)

Init == 
  /\ grid \in [Grid -> BOOLEAN]   \* any assignment of true/false to each cell
  /\ TypeOK

Tick == 
  /\ grid' = [p \in Grid |-> WillBeAlive(p)]
  /\ UNCHANGED << >>

Next == Tick

Spec == Init /\ [][Next]_<<grid>>

=============================================================================