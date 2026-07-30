---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat \ {0}

\* The state is a single mapping from positions to a boolean alive/dead value.
VARIABLES grid

Vars == <<grid>>

Positions == 1..N

Neighbors(p) ==
  {q \in Positions \X Positions :
     q # p /\ Cardinality({dx \in {-1, 0, 1}, dy \in {-1, 0, 1} :
       LET r == p[1] + dx
           c == p[2] + dy
       IN IF \A w \in {r, c} : w \in Positions THEN <<r, c>> ELSE p}) = 1}

LiveCount(p) == Cardinality({q \in Neighbors(p) : grid[q]})

TypeOK == grid \in [Positions \X Positions -> BOOLEAN]

Init ==
  \E g \in [Positions \X Positions -> BOOLEAN] : grid = g

Tick ==
  grid' = [p \in Positions \X Positions |->
              IF LiveCount(p) = 3 \/ (grid[p] /\ LiveCount(p) = 2)
              THEN TRUE
              ELSE FALSE]

Next == Tick

Spec == Init /\ [][Next]_Vars

====