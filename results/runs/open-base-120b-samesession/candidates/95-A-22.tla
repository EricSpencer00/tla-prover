---- MODULE GameOfLife ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

VARIABLE Grid

(*--- Positions on the N×N grid---*)
Pos == [i : 1..N, j : 1..N]

Abs(x) == IF x < 0 THEN -x ELSE x

Neighbors(p) == { q \in Pos :
                    (Abs(q.i - p.i) <= 1) /\ (Abs(q.j - p.j) <= 1) /\ ~(q = p) }

Count(p) == Cardinality( { q \in Neighbors(p) : Grid[q] } )

(*--- Initial state: any assignment of alive/dead cells---*)
Init == 
    /\ Grid \in [Pos -> BOOLEAN]

(*--- Simultaneous update according to Game of Life rules---*)
Next == 
    /\ Grid' = [p \in Pos |-> 
          IF Grid[p] 
             THEN (Count(p) = 2) \/ (Count(p) = 3) 
             ELSE Count(p) = 3 ]

Spec == Init /\ [][Next]_Grid

(*--- Type invariant---*)
TypeOK == Grid \in [Pos -> BOOLEAN]

====